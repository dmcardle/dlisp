use std::fmt::Display;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    ParseNum,
    Generic,
    NoToken,
    UnterminatedString,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::ParseNum => write!(f, "Error parsing number"),
            ParseError::Generic => write!(f, "Generic error"),
            ParseError::NoToken => write!(f, "Expected token"),
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

/// The purpose of [Tokenizer] is to iterate [Token] values from the given
/// string. Technically, it yields [Result<Token, ParseError>] values, which can
/// be collected into a [Result<Vec<Token>, ParseError>].
pub struct Tokenizer<'a> {
    view: &'a str,
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Token<'a>, ParseError>;

    /// Yield the next token result.
    fn next(&mut self) -> Option<Self::Item> {
        let mut chars = self.view.chars();
        match chars.next()? {
            ';' => {
                if let Some((n, c)) = self
                    .view
                    .char_indices()
                    .take_while(|(_, c)| *c != '\n')
                    .last()
                {
                    self.view = &self.view[n + 1..];
                }
                self.next()
            }
            '-' | '0'..='9' => Some(self.next_num()),
            'A'..='Z' | 'a'..='z' | '_' => Some(self.next_symbol()),
            c => {
                self.view = chars.as_str();
                match c {
                    ' ' | '\t' | '\r' | '\n' => self.next(),
                    '"' => Some(self.next_string()),
                    '(' => Some(Ok(Token::LeftParen)),
                    ')' => Some(Ok(Token::RightParen)),
                    '\'' => Some(Ok(Token::SingleQuote)),
                    _ => None,
                }
            }
        }
    }
}

impl<'a> Tokenizer<'a> {
    pub fn new(s: &str) -> Tokenizer {
        Tokenizer { view: &s }
    }

    fn next_num(&mut self) -> Result<Token<'a>, ParseError> {
        // Determine whether the number is negative.
        let mut char_indices = self.view.char_indices();
        let is_negative = match (char_indices.next(), char_indices.next()) {
            (None, _) => panic!("next_num expects one leading char"),
            (Some((_, '-')), Some((j, '0'..='9'))) => {
                // Consume the hyphen.
                self.view = &self.view[j..];
                true
            }
            (Some((_, '-')), Some((_, '-'))) => return Err(ParseError::ParseNum),
            (Some((_, '-')), Some((_, _))) => return Err(ParseError::ParseNum),
            _ => false,
        };
        // Parse a number composed of digits.
        let (i_end, value) = self
            .view
            .char_indices()
            .take_while(|(_, c)| c.is_numeric())
            .fold(Some((0usize, 0i32)), |acc, (i, c)| {
                let digit: i32 = (c as i32) - ('0' as i32);
                let (_, value) = acc?;
                let value = value.checked_mul(10)?.checked_add(digit)?;
                Some((i, value))
            })
            .ok_or(ParseError::ParseNum)?;
        // After parsing the number, consume all of its constituent characters.
        // Adding one to the index is safe because numeric characters are ASCII,
        // and thus take up a single byte.
        self.view = &self.view[i_end + 1..];

        Ok(Token::Num(if is_negative { -value } else { value }))
    }

    fn next_string(&mut self) -> Result<Token<'a>, ParseError> {
        // Proceed until we find the ending quote.
        let (i_end, is_escaping) =
            self.view
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
        match (i_end, is_escaping) {
            (Some(i), false) => {
                let body = &self.view[..i];
                // TODO Ensure that `i+1` is a UTF-8 boundary.
                self.view = &self.view[i + 1..];
                Ok(Token::String(body))
            }
            _ => Err(ParseError::UnterminatedString),
        }
    }

    fn next_symbol(&mut self) -> Result<Token<'a>, ParseError> {
        let len = self
            .view
            .chars()
            .take_while(|&c| c.is_alphanumeric() || c == '_')
            .count();
        if len == 0 {
            Err(ParseError::NoToken)
        } else {
            let symbol = &self.view[..len];
            self.view = &self.view[len..];
            Ok(Token::Symbol(symbol))
        }
    }
}

impl Token<'_> {
    pub fn lex(code: &str) -> Result<Vec<Token>, ParseError> {
        Tokenizer::new(&code).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_lex_whitespace() {
        assert_eq!(
            Token::lex("(print\t123\r\"abc\")\n"),
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
    fn test_lex_whitespace_trailing_tab() {
        assert_eq!(
            Token::lex("(print\t123\r\"abc\")\t"),
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
    fn test_tokenize_num_too_big() {
        let big_num_literal = format!("{}", i32::MAX as i64 + 1);
        assert_eq!(Token::lex(&big_num_literal), Err(ParseError::ParseNum));
    }

    #[test]
    fn test_tokenize_num_too_small() {
        let small_num_literal = format!("{}", i32::MIN as i64 - 1);
        assert_eq!(Token::lex(&small_num_literal), Err(ParseError::ParseNum));
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
    fn test_tokenize_comments() {
        assert_eq!(Token::lex(";hello\n"), Ok(vec![]));
        assert_eq!(Token::lex(";hello \n"), Ok(vec![]));
        assert_eq!(Token::lex(";hello\n42"), Ok(vec![Token::Num(42)]));
        assert_eq!(Token::lex("42;hello\n"), Ok(vec![Token::Num(42)]));
        assert_eq!(Token::lex("42;hello"), Ok(vec![Token::Num(42)]));
        assert_eq!(Token::lex(";hello"), Ok(vec![]));
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

    #[bench]
    fn bench_num_tokenize(b: &mut Bencher) {
        const MAX: u32 = 1000;
        b.iter(|| {
            for n in 0..MAX {
                // TODO: Figure out how to exclude this setup code from the
                // benchmark.
                let big_num: String = (0..n)
                    .map(|i: u32| char::from_u32(i % 10 + u32::from('0')).unwrap())
                    .collect();
                let _ = test::black_box(Token::lex(&big_num));
            }
        });
    }
}
