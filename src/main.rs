#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]

mod token;

use token::Token;
use token::ParseError;

use std::fmt::Display;
use std::io::Write;

#[derive(Debug)]
enum RuntimeError {
    Uncallable,
    Unprintable,
    Unaddable,
    UnknownFunction(String),
    WrongNumArgs { want: usize, got: usize },
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::Uncallable => write!(f, "Uncallable"),
            RuntimeError::Unprintable => write!(f, "Unprintable"),
            RuntimeError::Unaddable => write!(f, "Unaddable"),
            RuntimeError::UnknownFunction(s) => write!(f, "Unknown function {}", s),
            RuntimeError::WrongNumArgs { want, got } => {
                write!(f, "Wanted {} args, but got {}", want, got)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
enum Expr {
    Int(i32),
    String(String),
    Symbol(String),
    Application(Box<Expr>, Vec<Expr>),
    Quoted(Vec<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Int(n) => write!(f, "{}", n),
            Expr::String(s) => write!(f, "\"{}\"", s),
            Expr::Symbol(s) => write!(f, "'{}", s),
            Expr::Application(e, args) => {
                let args_repr = String::from_iter(args.iter().map(|a| format!(" {}", a)));
                write!(f, "({}{})", e, &args_repr)
            }
            Expr::Quoted(exprs) => write!(
                f,
                "(quote{})",
                String::from_iter(exprs.iter().map(|a| format!(" {}", a)))
            ),
        }
    }
}

impl Expr {
    pub fn parse(code: &str) -> Result<Expr, ParseError> {
        let tokens: Vec<Token> = Token::lex(code)?;
        let (expr, tail) = Self::parse_expr(&tokens)?;
        if tail.len() > 0 {
            println!("UNPARSED TAIL: {:?}", tail);
        }
        Ok(expr)
    }

    fn parse_expr<'a>(tokens: &'a [Token<'a>]) -> Result<(Expr, &'a [Token<'a>]), ParseError> {
        match tokens {
            [Token::Num(n), tail @ ..] => Ok((Expr::Int(*n), tail)),
            [Token::String(s), tail @ ..] => Ok((Expr::String(String::from(*s)), tail)),
            [Token::Symbol(s), tail @ ..] => Ok((Expr::Symbol(String::from(*s)), tail)),
            [Token::LeftParen, tail @ ..] => Self::parse_application(tail),
            [Token::RightParen, ..] => Err(ParseError::Generic),
            [Token::SingleQuote, ..] => Err(ParseError::Generic),
            [] => Err(ParseError::EmptyString),
        }
    }

    fn parse_application<'a>(
        tokens: &'a [Token<'a>],
    ) -> Result<(Expr, &'a [Token<'a>]), ParseError> {
        let (left, arg_tokens) = Self::parse_expr(tokens)?;

        let mut right = Vec::new();
        let mut arg_tokens = arg_tokens;
        while let Ok((expr, tail)) = Self::parse_expr(arg_tokens) {
            right.push(expr);
            arg_tokens = tail;
        }
        match arg_tokens {
            [Token::RightParen, tail @ ..] => {
                let application = Expr::Application(Box::new(left), right);
                Ok((application, tail))
            }
            _ => Err(ParseError::Generic),
        }
    }

    pub fn eval(expr: Expr) -> Result<Expr, RuntimeError> {
        match expr {
            Expr::Int(_) => Ok(expr),
            Expr::String(_) => Ok(expr),
            Expr::Symbol(_) => Ok(expr),
            Expr::Quoted(_) => Ok(expr),
            Expr::Application(boxed_expr, args) => match *boxed_expr {
                Expr::Symbol(func_name) => match func_name.as_str() {
                    "quote" => Ok(Expr::Quoted(args)),
                    "cond" => Self::builtin_cond(args),
                    "print" => Self::builtin_print(args),
                    "add" => Self::builtin_add(args),
                    _ => Err(RuntimeError::UnknownFunction(func_name)),
                },
                _ => Err(RuntimeError::Uncallable),
            },
        }
    }

    fn builtin_cond(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
        const NUM_ARGS: usize = 3;
        if args.len() != NUM_ARGS {
            return Err(RuntimeError::WrongNumArgs {
                want: NUM_ARGS,
                got: args.len(),
            });
        }

        let mut args = args;
        let e2 = args.pop().unwrap();
        let e1 = args.pop().unwrap();
        let selector = args.pop().unwrap();

        match Expr::eval(selector)? {
            Expr::Int(0) => Expr::eval(e2),
            _ => Expr::eval(e1),
        }
    }

    fn builtin_print(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
        let mut pieces = Vec::new();
        for arg in args {
            match Self::eval(arg)? {
                Expr::Int(n) => {
                    pieces.push(format!("{}", n));
                }
                Expr::String(s) => {
                    pieces.push(format!("{}", s));
                }
                Expr::Symbol(s) => {
                    pieces.push(format!("{}", s));
                }
                Expr::Quoted(expr) => {
                    pieces.push(format!("{:?}", expr));
                }
                Expr::Application(_, _) => {
                    return Err(RuntimeError::Unprintable);
                }
            }
        }
        let joined = pieces.join(" ");
        println!("{}", joined);
        Ok(Expr::String(joined))
    }

    fn builtin_add(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
        let mut sum = 0;
        for arg in args {
            match Self::eval(arg)? {
                Expr::Int(n) => {
                    sum += n;
                }
                _ => {
                    return Err(RuntimeError::Unaddable);
                }
            }
        }
        Ok(Expr::Int(sum))
    }
}

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

        match Token::lex(&buffer) {
            Ok(tokens) => {
                // If there's a single token, we may want to interpret it as a
                // REPL command.
                if tokens.len() == 1 {
                    match &tokens[0] {
                        Token::Symbol("quit") | Token::Symbol("q") => {
                            return;
                        }
                        _ => {}
                    }
                }
            }
            Err(e) => {
                println!("Error while tokenizing: {}", e);
            }
        }

        let expr = Expr::parse(&buffer);
        if let Ok(expr) = expr {
            match Expr::eval(expr) {
                Ok(value) => {
                    println!("{}", value);
                }
                Err(e) => {
                    println!("ERROR {}", e);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display_expr_int() {
        assert_eq!(format!("{}", Expr::Int(0)), "0");
        assert_eq!(format!("{}", Expr::Int(1)), "1");
        assert_eq!(format!("{}", Expr::Int(123)), "123");
        assert_eq!(format!("{}", Expr::Int(-123)), "-123");
    }

    #[test]
    fn test_display_expr_string() {
        assert_eq!(format!("{}", Expr::String("".to_string())), "\"\"");
        assert_eq!(format!("{}", Expr::String("abc".to_string())), "\"abc\"");
        assert_eq!(format!("{}", Expr::String("\\".to_string())), "\"\\\"");
    }

    #[test]
    fn test_display_expr_symbol() {
        // TODO Disallow the empty symbol.
        assert_eq!(format!("{}", Expr::Symbol("".to_string())), "'");
        assert_eq!(format!("{}", Expr::Symbol("foo".to_string())), "'foo");
    }

    #[test]
    fn test_display_expr_application() {
        assert_eq!(
            format!(
                "{}",
                Expr::Application(
                    Box::new(Expr::Symbol("add".to_string())),
                    vec![Expr::Int(1), Expr::Int(2)]
                )
            ),
            "('add 1 2)"
        );
    }

    #[test]
    fn test_display_expr_quoted() {
        assert_eq!(
            format!(
                "{}",
                Expr::Quoted(vec![
                    Expr::Symbol("f".to_string()),
                    Expr::Int(1),
                    Expr::Int(2)
                ])
            ),
            "(quote 'f 1 2)"
        );
    }

    #[test]
    fn test_parse() {
        assert_eq!(
            Expr::parse("(print 123 \"abc\")"),
            Ok(Expr::Application(
                Box::new(Expr::Symbol(String::from("print"))),
                vec![Expr::Int(123), Expr::String(String::from("abc")),]
            ))
        );
    }

    #[test]
    fn test_cond() {
        let expr = Expr::parse("(cond 0 \"truth\" \"lies\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse("(cond 1 \"truth\" \"lies\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse("(cond 2 \"truth\" \"lies\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse("(cond \"x\" \"truth\" \"lies\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_selector() {
        let expr = Expr::parse("(cond (add 0 0) \"truth\" \"lies\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse("(cond (add 1 0) \"truth\" \"lies\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_result() {
        let expr = Expr::parse("(cond 1 (cond 0 \"a\" \"b\") \"c\")").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));

        let expr = Expr::parse("(cond 0 \"c\" (cond 0 \"a\" \"b\"))").unwrap();
        let expr = Expr::eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));
    }
}
