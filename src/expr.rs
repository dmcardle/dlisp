use crate::token::ParseError;
use crate::token::Token;

use std::fmt::Display;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Nil,
    True,
    Int(i32),
    String(String),
    Symbol(String),
    Application(Box<Expr>, Vec<Expr>),
    Quoted(Vec<Expr>),
    Def(String, Box<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Nil => write!(f, "nil"),
            Expr::True => write!(f, "true"),
            Expr::Int(n) => write!(f, "{}", n),
            Expr::String(s) => write!(f, "\"{}\"", s),
            Expr::Symbol(s) => write!(f, "{}", s),
            Expr::Application(e, args) => {
                let args_repr = String::from_iter(args.iter().map(|a| format!(" {}", a)));
                write!(f, "({}{})", e, &args_repr)
            }
            Expr::Quoted(exprs) => write!(
                f,
                "(quote{})",
                String::from_iter(exprs.iter().map(|a| format!(" {}", a)))
            ),
            Expr::Def(name, expr) => write!(f, "(def {name} {expr})"),
        }
    }
}

impl Expr {
    pub fn parse_str(code: &str) -> Result<Expr, ParseError> {
        let tokens: Vec<Token> = Token::lex(code)?;
        Expr::parse(&tokens)
    }

    pub fn parse(tokens: &[Token]) -> Result<Expr, ParseError> {
        let (expr, tail) = Self::parse_expr(tokens)?;
        if !tail.is_empty() {
            println!("UNPARSED TAIL: {:?}", tail);
        }
        Ok(expr)
    }

    fn parse_expr<'a>(tokens: &'a [Token<'a>]) -> Result<(Expr, &'a [Token<'a>]), ParseError> {
        match tokens {
            [Token::Num(n), tail @ ..] => Ok((Expr::Int(*n), tail)),
            [Token::String(s), tail @ ..] => Ok((Expr::String(String::from(*s)), tail)),
            [Token::Symbol("nil"), tail @ ..] => Ok((Expr::Nil, tail)),
            [Token::Symbol("true"), tail @ ..] => Ok((Expr::True, tail)),
            [Token::Symbol(s), tail @ ..] => Ok((Expr::Symbol(String::from(*s)), tail)),
            [Token::LeftParen, tail @ ..] => Self::parse_application(tail),
            [Token::RightParen, ..] => Err(ParseError::Generic),
            [Token::SingleQuote, ..] => Err(ParseError::Generic),
            [] => Err(ParseError::NoToken),
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
                // Depending on the `left` expr, we may want to produce a more
                // specialized type than `Expr::Application`.
                match left {
                    Expr::Symbol(symbol) => match symbol.as_str() {
                        "quote" => {
                            let quoted = Expr::Quoted(right);
                            Ok((quoted, tail))
                        }
                        "def" => match right.as_slice() {
                            [Expr::Symbol(name), body] => {
                                let definition =
                                    Expr::Def(name.to_string(), Box::new(body.clone()));
                                Ok((definition, tail))
                            }
                            _ => Err(ParseError::Generic),
                        },
                        _ => {
                            let application =
                                Expr::Application(Box::new(Expr::Symbol(symbol)), right);
                            Ok((application, tail))
                        }
                    },
                    _ => Err(ParseError::Generic),
                }
            }
            _ => Err(ParseError::Generic),
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
        assert_eq!(format!("{}", Expr::Symbol("".to_string())), "");
        assert_eq!(format!("{}", Expr::Symbol("foo".to_string())), "foo");
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
            "(add 1 2)"
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
            "(quote f 1 2)"
        );
    }

    #[test]
    fn test_parse() {
        assert_eq!(
            Expr::parse_str("(print 123 \"abc\")"),
            Ok(Expr::Application(
                Box::new(Expr::Symbol(String::from("print"))),
                vec![Expr::Int(123), Expr::String(String::from("abc")),]
            ))
        );
    }

    #[test]
    fn test_parse_quote() {
        assert_eq!(
            Expr::parse_str("(quote 123 \"abc\")"),
            Ok(Expr::Quoted(vec![
                Expr::Int(123),
                Expr::String(String::from("abc"))
            ]))
        );
    }
}
