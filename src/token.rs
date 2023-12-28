use std::fmt::Display;

#[derive(Debug, PartialEq)]
pub enum ParseError {
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

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    Num(i32),
    String(&'a str),
    Symbol(&'a str),
    LeftParen,
    RightParen,
    SingleQuote,
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

    /// Return the next token and the unlexed remainder of the given string.
    ///
    /// TODO: Refactor these methods into a `Tokenizer` struct that mutates a
    /// single `&str`. I think this will simplify some of this logic where we
    /// repeatedly figure out what the suffix should be.
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

    extern crate test;
    use test::Bencher;

    #[bench]
    fn bench_string_tokenize(b: &mut Bencher) {
        const MAX: usize = 1000;
        b.iter(|| {
            for n in 0..MAX {
                // TODO: Figure out how to exclude this setup code from the
                // benchmark.
                let big_string: String = std::iter::once('"')
                    .chain((0..n).map(|i| char::from_u32(i as u32 % 256).unwrap()))
                    .chain(std::iter::once('"'))
                    .collect();
                let _ = test::black_box(Token::lex(&big_string));
            }
        });
    }
}
