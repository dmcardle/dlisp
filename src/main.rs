#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![feature(test)]
#![feature(assert_matches)]

mod eval;
mod expr;
mod token;

use std::io::Write;

use eval::eval;
use expr::Expr;

fn main() -> Result<(), String> {
    loop {
        print!(">>> ");
        if std::io::stdout().flush().is_err() {
            println!("Failed to flush stdout");
        }

        let mut buffer = String::new();
        if std::io::stdin().read_line(&mut buffer).is_err() {
            println!("Failed to read from stdin");
            return Ok(());
        }

        // Peek at the first token from stdin.
        let first_token = token::Tokenizer::new(&buffer).next();
        match first_token {
            Some(Ok(token::Token::Symbol("quit"))) => return Ok(()),
            _ => {}
        };

        // Evaluate and print the string from stdin.
        let expr_result: Expr = eval(&buffer).map_err(|e| format!("{}", e))?;
        println!("{}", expr_result);
    }
}
