#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![feature(test)]
#![feature(assert_matches)]
#![feature(iterator_try_collect)]

mod eval;
mod expr;
mod token;

use std::io::Write;

use eval::Evaluator;
use expr::Expr;

fn main() -> Result<(), String> {
    const PROMPT: &str = "";
    let mut evaluator = Evaluator::new();

    // TODO: Figure out how to support multi-line expressions.
    let stdlib = std::include_bytes!("../stdlib.dl");
    let stdlib = std::str::from_utf8(stdlib).expect("stdlib must be utf-8");
    for line in stdlib.lines() {
        let line = line.trim();
        println!("{PROMPT}{line}");
        evaluator.eval(&line).map_err(|e| format!("{}", e))?;
    }

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
        match first_token {
            Some(Ok(token::Token::Symbol("quit"))) => return Ok(()),
            _ => {}
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
