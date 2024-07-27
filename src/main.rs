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
use token::{Token, Tokenizer};

fn main() -> Result<(), String> {
    let mut evaluator = Evaluator::new();

    // TODO: Figure out how to support multi-line expressions.
    let stdlib = std::include_bytes!("../stdlib.dl");
    let stdlib = std::str::from_utf8(stdlib).expect("stdlib must be utf-8");
    let stdlib_tokens = Token::lex(stdlib).map_err(|e| e.to_string())?;

    let mut last_i = 0;
    let mut depth = 0;
    for (i, t) in stdlib_tokens.iter().enumerate() {
        match &t {
            Token::LeftParen => depth += 1,
            Token::RightParen => depth -= 1,
            _ => {}
        };
        if depth == 0 {
            // Select the tokens for a single expr.
            let tokens = &stdlib_tokens[last_i..=i];
            last_i = i + 1;

            let expr = Expr::parse(&tokens).map_err(|e| format!("Parse error: {}", e))?;
            println!("stdlib: {expr}");
            evaluator
                .eval_expr(&expr)
                .map_err(|e| format!("Eval error: {}", e))?;
        }
    }
    if depth > 0 {
        return Err(String::from("Unterminated expression in stdlib."));
    }

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
