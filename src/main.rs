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
    let mut evaluator = Evaluator::new();
    loop {
        print!("::: ");
        if std::io::stdout().flush().is_err() {
            println!("Failed to flush stdout");
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
            Ok(expr) => println!("{}", expr),
            Err(err) => println!("! {}", err),
        }
    }
}
