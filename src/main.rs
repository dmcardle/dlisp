#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]

use std::fmt::Display;
use std::io::Write;

#[derive(Debug, PartialEq)]
enum Token<'a> {
    Num(i32),
    String(&'a str),
    Symbol(&'a str),
    LeftParen,
    RightParen,
    SingleQuote,
}

#[derive(Debug, PartialEq)]
enum ParseError {
    ParseNum,
    Generic,
    EmptyString,
    UnterminatedString,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::ParseNum => write!(f, "Error parsing number"),
            ParseError::Generic => write!(f, "Generic error"),
            ParseError::EmptyString => write!(f, "Expected token"),
            ParseError::UnterminatedString => write!(f, "Unterminated string literal"),
        }
    }
}

impl Token<'_> {
    pub fn lex(code: &str) -> Result<Vec<Token>, ParseError> {
        let mut out = Vec::new();
        let mut token_buf: &str = &code;
        while token_buf.len() > 0 && token_buf != "\n" {
            let (token, tail) = Token::eat_token(&token_buf)?;
            out.push(token);
            token_buf = tail;
        }
        Ok(out)
    }

    fn eat_token(s: &str) -> Result<(Token, &str), ParseError> {
        if s.len() == 0 {
            return Err(ParseError::EmptyString);
        }
        let mut chars = s.chars().peekable();
        match chars.peek().ok_or(ParseError::Generic)? {
            ' ' => Token::eat_token(&s[1..]),
            '-' | '0'..='9' => Token::eat_num_token(&s),
            '"' => Token::eat_string_token(&s[1..]),
            'A'..='Z' | 'a'..='z' | '_' => Token::eat_symbol_token(&s),
            '(' => Ok((Token::LeftParen, &s[1..])),
            ')' => Ok((Token::RightParen, &s[1..])),
            '\'' => Ok((Token::SingleQuote, &s[1..])),
            _ => Err(ParseError::Generic),
        }
    }

    fn eat_num_token(s: &str) -> Result<(Token, &str), ParseError> {
        assert_ne!(s.len(), 0);
        println!("eat_num_token: {}", s);

        let is_negative = s.chars().next().unwrap() == '-';
        if let Some(c) = s.chars().skip(1).next() {
            if c == '-' {
                return Err(ParseError::ParseNum);
            }
        }

        let mut chars = s.chars();
        if is_negative {
            chars.next();
        }

        let orig_len = chars.as_str().len();

        let mut value: i32 = 0;
        let mut suffix = s;
        while let Some(c) = chars.next() {
            match c {
                '0'..='9' => {
                    value = 10 * value + ((c as i32) - ('0' as i32));
                    suffix = chars.as_str();
                }
                _ => break,
            }
        }

        if chars.as_str().len() == orig_len {
            Err(ParseError::ParseNum)
        } else {
            if is_negative {
                value *= -1;
            }
            Ok((Token::Num(value), suffix))
        }
    }

    /// Consume the remainder of a string literal, assuming the opening
    /// quotation mark has already been consumed.
    fn eat_string_token(s: &str) -> Result<(Token, &str), ParseError> {
        let (i_end, _) = s
            .char_indices()
            .fold((None, false), |(i_end, is_escaping), (i, c)| {
                match (i_end, c, is_escaping) {
                    #![rustfmt::skip]
                    // If we've already found the end, pass it on.
                    (Some(i),    _,           _) => (Some(i),        false),
                    // If we found a quotation mark, we may have found the end
                    // of the string literal!
                    (      _,  '"',       false) => (Some(i),        false),
                    (      _,  '"',        true) => (   None,        false),
                    // Backslashes are never the end of a string literal, but
                    // they do affect escaping. If we were already escaping,
                    // this is a true backlsash. Otherwise, escape the next
                    // character.
                    (      _, '\\', is_escaping) => (   None, !is_escaping),
                    // Regular characters have no special semantics. Disable
                    // escaping and move on.
                                               _ => (   None,        false),
                }
            });
        match i_end {
            Some(i) => Ok((Token::String(&s[..i]), &s[i + 1..])),
            _ => Err(ParseError::UnterminatedString),
        }
    }

    fn eat_symbol_token(s: &str) -> Result<(Token, &str), ParseError> {
        let len = s
            .chars()
            .take_while(|&c| c.is_alphanumeric() || c == '_')
            .count();
        Ok((Token::Symbol(&s[..len]), &s[len..]))
    }
}

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
                write!(f, "(")?;
                write!(f, "{}", e)?;
                write!(
                    f,
                    "{}",
                    args.iter()
                        .map(|a| format!("{}", a))
                        .fold(String::new(), |a, b| format!("{} {}", a, b))
                )?;
                write!(f, ")")
            }
            Expr::Quoted(exprs) => write!(
                f,
                "(quote {})",
                exprs
                    .iter()
                    .map(|a| format!("{}", a))
                    .fold(String::new(), |a, b| format!("{} {}", a, b))
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
    fn simple_tokenizing() {
        assert_eq!(Token::eat_token("123 )"), Ok((Token::Num(123), " )")));
        assert_eq!(Token::eat_token("(foo)"), Ok((Token::LeftParen, "foo)")));
        assert_eq!(Token::eat_token(" foo )"), Ok((Token::Symbol("foo"), " )")));
        assert_eq!(Token::eat_token("foo )"), Ok((Token::Symbol("foo"), " )")));
        assert_eq!(
            Token::eat_token(" \"abc\")"),
            Ok((Token::String("abc"), ")"))
        );
    }

    #[test]
    fn test_lex() {
        assert_eq!(
            Token::lex("(print 123 \"abc\")"),
            Ok(vec![
                Token::LeftParen,
                Token::Symbol("print"),
                Token::Num(123),
                Token::String("abc"),
                Token::RightParen,
            ])
        );
    }

    #[test]
    fn test_tokenize_num() {
        assert_eq!(Token::lex("0"), Ok(vec![Token::Num(0)]));
        assert_eq!(Token::lex("123"), Ok(vec![Token::Num(123)]));
        assert_eq!(Token::lex("-0"), Ok(vec![Token::Num(0)]));
        assert_eq!(Token::lex("-123"), Ok(vec![Token::Num(-123)]));
        assert_eq!(Token::lex("--123"), Err(ParseError::ParseNum));
        assert_eq!(Token::lex("---123"), Err(ParseError::ParseNum));

        // TODO: support hexadecimal number literals.
        assert_eq!(
            Token::lex("0x123"),
            Ok(vec![Token::Num(0), Token::Symbol("x123")])
        );
    }

    #[test]
    fn test_tokenize_string() {
        // Empty string.
        assert_eq!(Token::lex("\"\""), Ok(vec![Token::String("")]));
        // Single character strings.
        assert_eq!(Token::lex("\"a\""), Ok(vec![Token::String("a")]));
        assert_eq!(Token::lex("\" \""), Ok(vec![Token::String(" ")]));
        // Strings with spaces.
        assert_eq!(Token::lex("\" a \""), Ok(vec![Token::String(" a ")]));
        assert_eq!(Token::lex("\"a \""), Ok(vec![Token::String("a ")]));
        assert_eq!(Token::lex("\" a\""), Ok(vec![Token::String(" a")]));
        // Multi-character strings with no spaces.
        assert_eq!(Token::lex("\"foo\""), Ok(vec![Token::String("foo")]));
        // Unterminated string literals.
        assert_eq!(Token::lex("\""), Err(ParseError::UnterminatedString));
        assert_eq!(Token::lex("\"foo"), Err(ParseError::UnterminatedString));
    }

    #[test]
    fn test_tokenize_string_escaping() {
        assert_eq!(Token::lex("\""), Err(ParseError::UnterminatedString));
        assert_eq!(Token::lex("\"\\"), Err(ParseError::UnterminatedString));
        assert_eq!(Token::lex("\"foo\\\""), Err(ParseError::UnterminatedString));
        assert_eq!(
            Token::lex("\"foo\\\"\""),
            Ok(vec![Token::String("foo\\\"")])
        );
        assert_eq!(Token::lex(r#""\\\""#), Err(ParseError::UnterminatedString));
        assert_eq!(Token::lex(r#""\\\\""#), Ok(vec![Token::String(r#"\\\\"#)]));
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
