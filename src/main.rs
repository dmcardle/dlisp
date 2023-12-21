use std::io::Write;

#[derive(Debug, PartialEq)]
enum Expr {
    AtomNum(i32),
    AtomStr(String),
    Symbol(String),
    Application(Box<Expr>, Vec<Expr>),
    Quoted(Vec<Expr>),
}

#[derive(Debug, PartialEq)]
enum Token<'a> {
    Num(i32),
    String(&'a str),
    Symbol(&'a str),
    LeftParen,
    RightParen,
    SingleQuote,
}

impl Token<'_> {
    pub fn eat_token(s: &str) -> Result<(Token, &str), ParseError> {
        if s.len() == 0 {
            return Err(ParseError::EmptyString);
        }
        let mut chars = s.chars().peekable();
        match chars.peek().ok_or(ParseError::Generic)? {
            ' ' => Token::eat_token(&s[1..]),
            '0'..='9' => Token::eat_num_token(&s),
            '"' => Token::eat_string_token(&s[1..]),
            'A'..='Z' | 'a'..='z' | '_' => Token::eat_symbol_token(&s),
            '(' => Ok((Token::LeftParen, &s[1..])),
            ')' => Ok((Token::RightParen, &s[1..])),
            '\'' => Ok((Token::SingleQuote, &s[1..])),
            _ => Err(ParseError::Generic),
        }
    }

    fn eat_num_token(s: &str) -> Result<(Token, &str), ParseError> {
        let len = s.chars().take_while(|c| c.is_numeric()).count();
        if len == 0 {
            return Err(ParseError::ParseNum);
        }
        if let Ok(n) = s[0..len].parse::<i32>() {
            Ok((Token::Num(n), &s[len..]))
        } else {
            Err(ParseError::ParseNum)
        }
    }

    fn eat_string_token(s: &str) -> Result<(Token, &str), ParseError> {
        // TODO: support backslash escaping.
        let len = s.chars().take_while(|&c| c != '"').count();
        Ok((Token::String(&s[0..len]), &s[len + 1..]))
    }
    fn eat_symbol_token(s: &str) -> Result<(Token, &str), ParseError> {
        let len = s
            .chars()
            .take_while(|&c| c.is_alphanumeric() || c == '_')
            .count();
        Ok((Token::Symbol(&s[..len]), &s[len..]))
    }
}

#[derive(Debug, PartialEq)]
enum ParseError {
    ParseNum,
    Generic,
    EmptyString,
}

fn lex(code: &str) -> Result<Vec<Token>, ParseError> {
    let mut out = Vec::new();
    let mut token_buf: &str = &code;
    while token_buf.len() > 0 && token_buf != "\n" {
        let (token, tail) = Token::eat_token(&token_buf)?;
        out.push(token);
        token_buf = tail;
    }
    Ok(out)
}

fn parse_application<'a>(tokens: &'a [Token<'a>]) -> Result<(Expr, &'a [Token<'a>]), ParseError> {
    let (left, arg_tokens) = parse_expr(tokens)?;

    let mut right = Vec::new();
    let mut arg_tokens = arg_tokens;
    while let Ok((expr, tail)) = parse_expr(arg_tokens) {
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

fn parse_expr<'a>(tokens: &'a [Token<'a>]) -> Result<(Expr, &'a [Token<'a>]), ParseError> {
    match tokens {
        [Token::Num(n), tail @ ..] => Ok((Expr::AtomNum(*n), tail)),
        [Token::String(s), tail @ ..] => Ok((Expr::AtomStr(String::from(*s)), tail)),
        [Token::Symbol(s), tail @ ..] => Ok((Expr::Symbol(String::from(*s)), tail)),
        [Token::LeftParen, tail @ ..] => parse_application(tail),
        [Token::RightParen, ..] => Err(ParseError::Generic),
        [Token::SingleQuote, ..] => Err(ParseError::Generic),
        [] => Err(ParseError::EmptyString),
    }
}

fn parse(code: &str) -> Result<Expr, ParseError> {
    let tokens: Vec<Token> = lex(code)?;
    let (expr, tail) = parse_expr(&tokens)?;
    if tail.len() > 0 {
        println!("UNPARSED TAIL: {:?}", tail);
    }
    Ok(expr)
}

#[derive(Debug)]
enum RuntimeError {
    Uncallable,
    Unprintable,
    Unaddable,
    UnknownFunction(String),
}

fn builtin_print(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
    let mut pieces = Vec::new();
    for arg in args {
        match eval(arg)? {
            Expr::AtomNum(n) => {
                pieces.push(format!("{}", n));
            }
            Expr::AtomStr(s) => {
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
    Ok(Expr::AtomStr(joined))
}

fn builtin_add(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
    let mut sum = 0;
    for arg in args {
        match eval(arg)? {
            Expr::AtomNum(n) => {
                sum += n;
            }
            _ => {
                return Err(RuntimeError::Unaddable);
            }
        }
    }
    Ok(Expr::AtomNum(sum))
}

fn eval(expr: Expr) -> Result<Expr, RuntimeError> {
    match expr {
        Expr::AtomNum(_) => Ok(expr),
        Expr::AtomStr(_) => Ok(expr),
        Expr::Symbol(_) => Ok(expr),
        Expr::Quoted(_) => Ok(expr),
        Expr::Application(boxed_expr, args) => match *boxed_expr {
            Expr::Symbol(func_name) => match func_name.as_str() {
                "quote" => Ok(Expr::Quoted(args)),
                "print" => builtin_print(args),
                "add" => builtin_add(args),
                _ => Err(RuntimeError::UnknownFunction(func_name)),
            },
            _ => Err(RuntimeError::Uncallable),
        },
    }
}

fn main() {
    println!("{:?}", lex("( print 42 )"));

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

        match lex(&buffer) {
            Ok(tokens) => {
                println!("Tokenized: {:?}", tokens);

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
            err => {
                println!("Error while tokenizing: {:?}", err);
            }
        }

        let expr = parse(&buffer);
        println!("Parsed: {:?}", expr);
        if let Ok(expr) = expr {
            println!("Evaluated: {:?}", eval(expr));
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
            lex("(print 123 \"abc\")"),
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
    fn test_parse() {
        assert_eq!(
            parse("(print 123 \"abc\")"),
            Ok(Expr::Application(
                Box::new(Expr::Symbol(String::from("print"))),
                vec![Expr::AtomNum(123), Expr::AtomStr(String::from("abc")),]
            ))
        );
    }
}
