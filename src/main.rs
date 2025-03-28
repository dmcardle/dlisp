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

    args.next()
        .ok_or("expected first arg to be path to dlisp")?;

    match args.next() {
        None => repl(evaluator),

        Some(help) if help == "-h" || help == "--help" => {
            let description = std::include_str!("../README.md").trim_end();
            println!(
                "{description}

Usage: dlisp [SOURCE [ARGS...]]
       dlisp (-h | --help)"
            );
            Ok(())
        }

        Some(src_path) => {
            let remaining_args: Vec<String> = args.collect();

            let code = std::fs::read_to_string(src_path).map_err(|x| x.to_string())?;
            load(&mut evaluator, &code)?;

            // If the script defined a function named "main", that will be our
            // entry point. Synthesize a call to `main` and pass any remaining
            // command-line arguments.
            const MAIN: &str = "main";
            if let Some(Expr::Def(..)) = evaluator.env.get(MAIN) {
                let main = Expr::Symbol(MAIN.into());
                let args = Expr::Quoted(
                    remaining_args
                        .iter()
                        .map(|s| Expr::String(s.clone()))
                        .collect(),
                );
                evaluator
                    .eval_expr(&Expr::Application(main.into(), vec![args]))
                    .map_err(|e| e.to_string())?;
            }
            Ok(())
        }
    }
}

fn load(evaluator: &mut Evaluator, code: &str) -> Result<(), String> {
    let tokens = Token::lex(code).map_err(|e| e.to_string())?;
    let _ = eval_tokens(evaluator, &tokens).map_err(|err| err.to_string())?;
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

fn eval_tokens(evaluator: &mut Evaluator, tokens: &[Token]) -> Result<Expr, String> {
    let mut last_i = 0;
    let mut depth = 0;
    for (i, t) in tokens.iter().enumerate() {
        match &t {
            Token::LeftParen => depth += 1,
            Token::RightParen => depth -= 1,
            _ => {}
        };
        if depth == 0 {
            // Select the tokens for a single expr.
            let tokens = &tokens[last_i..=i];
            last_i = i + 1;

            let expr = Expr::parse(tokens).map_err(|err| err.to_string())?;
            evaluator.eval_expr(&expr).map_err(|err| err.to_string())?;
        }
    }
    if depth > 0 {
        return Err(format!(
            "Evaluator is at depth {depth}; some tokens must be missing"
        ));
    }

    Ok(Expr::Nil)
}
