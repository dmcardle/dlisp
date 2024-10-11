#![feature(box_patterns)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![feature(test)]
#![feature(assert_matches)]
#![feature(iterator_try_collect)]

mod eval;
mod expr;
mod token;

use std::env;
use std::io::Write;

use eval::Evaluator;
use expr::Expr;
use token::Token;

fn main() -> Result<(), String> {
    let mut evaluator = Evaluator::new();

    let stdlib = std::include_bytes!("../stdlib.lisp");
    let stdlib = std::str::from_utf8(stdlib).expect("stdlib must be utf-8");
    load(&mut evaluator, stdlib)?;

    let mut args = env::args();
    let _command = args
        .next()
        .ok_or("expected first arg to be path to dlisp")?;

    let args_tail: Vec<String> = args.collect();
    match &args_tail[..] {
        // When there are no args, run the REPL.
        [] => repl(evaluator),

        // The first arg should be a path to a file containing some dlisp code.
        // Load and run the code!
        [src_path, remaining_args @ ..] => {
            let code = std::fs::read_to_string(src_path).map_err(|x| x.to_string())?;
            load(&mut evaluator, &code)?;

            // When the script defined a function named "main", synthesize a
            // call to the function that passes along this program's argv.
            if let Some(Expr::Def(..)) = evaluator.env.get("main") {
                let target = Box::new(Expr::Symbol("main".to_string()));
                let quoted_argv = Expr::Quoted(
                    remaining_args
                        .iter()
                        .map(|s| Expr::String(s.clone()))
                        .collect(),
                );
                let call_main_expr = Expr::Application(target, vec![quoted_argv]);

                evaluator
                    .eval_expr(&call_main_expr)
                    .map_err(|e| e.to_string())?;
            }

            Ok(())
        }
    }
}

fn load(evaluator: &mut Evaluator, code: &str) -> Result<(), String> {
    let tokens = Token::lex(code).map_err(|e| e.to_string())?;
    let _ = evaluator
        .eval_tokens(&tokens)
        .map_err(|err| format!("Error: {err}"))?;
    Ok(())
}

fn repl(mut evaluator: Evaluator) -> Result<(), String> {
    // The prompt must be non-empty because we do not print nil results.
    // Printing the prompt tells the user implicitly that their expression was
    // evaluated.
    const PROMPT: &str = "::: ";

    println!("{}", PROMPT);

    loop {
        print!("{}", PROMPT);
        if std::io::stdout().flush().is_err() {
            println!("Failed to flush stdout");
            return Ok(());
        }

        let mut buffer = String::new();
        if std::io::stdin().read_line(&mut buffer).is_err() {
            println!("Failed to read from stdin");
            return Ok(());
        }

        if buffer == "\n" {
            continue;
        }

        // Peek at the first token from stdin.
        let first_token = token::Tokenizer::new(&buffer).next();
        if let Some(Ok(token::Token::Symbol("quit"))) = first_token {
            return Ok(());
        };

        // Evaluate and print the string from stdin.
        let expr_result = evaluator.eval(&buffer).map_err(|e| format!("{}", e));
        match expr_result {
            Ok(Expr::Nil) => {}
            Ok(expr) => println!("-> {}", expr),
            Err(err) => println!("! {}", err),
        }
    }
}
