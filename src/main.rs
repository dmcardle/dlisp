#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![feature(test)]

mod eval;
mod expr;
mod token;

use std::io::Write;

use eval::eval;
use expr::Expr;
use token::Token;

fn main() {
    loop {
        print!(">>> ");
        if std::io::stdout().flush().is_err() {
            println!("Failed to flush stdout");
        }

        let mut buffer = String::new();
        if std::io::stdin().read_line(&mut buffer).is_err() {
            println!("Failed to read from stdin");
            return;
        }

        match Token::lex(&buffer).as_deref() {
            // If there's a single token, we may want to interpret it as a REPL
            // command.
            Ok([Token::Symbol("quit")]) => {
                return;
            }
            Ok(tokens) => {
                let expr = Expr::parse(&tokens);
                if let Ok(expr) = expr {
                    match eval(expr) {
                        Ok(value) => {
                            println!("{}", value);
                        }
                        Err(e) => {
                            println!("ERROR {}", e);
                        }
                    }
                }
            }
            Err(e) => {
                println!("Error while tokenizing: {}", e);
            }
        }
    }
}
