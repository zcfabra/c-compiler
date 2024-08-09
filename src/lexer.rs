use crate::token::Token;
use std::fmt::Display;

#[derive(Debug, PartialEq, Eq)]
enum InvalidIdentifierReason {
    StartsWithNumber,
}

impl Display for InvalidIdentifierReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            Self::StartsWithNumber => "Identifier Cannot Start With Number",
        };
        write!(f, "{}", msg)
    }
}

#[derive(Debug, PartialEq, Eq)]
enum LexError {
    UnknownToken(IndexedCh),
    InvalidIdentifier((String, InvalidIdentifierReason)),
}

impl LexError {
    fn to_string(&self) -> String {
        match self {
            Self::UnknownToken((ix, ch)) => {
                format!(
                    "Found Unknown Character `{}` at position `{}`",
                    ch, ix
                )
            }
            Self::InvalidIdentifier((str, reason)) => {
                format!("Invalid Identifer: `{}` - {}", str, reason)
            }
        }
    }
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

type IndexedCh = (u32, char);

struct Lexer<I>
where
    I: Iterator<Item = IndexedCh>,
{
    contents: I,
    curr_ch: Option<IndexedCh>,
    peek_ch: Option<IndexedCh>,
}

impl<I> Lexer<I>
where
    I: Iterator<Item = IndexedCh>,
{
    pub fn new(contents: I) -> Self {
        let mut l = Lexer {
            contents: contents,
            curr_ch: None,
            peek_ch: None,
        };
        let _ = l.next_char();
        let _ = l.next_char();
        return l;
    }

    pub fn next_char(&mut self) -> Option<IndexedCh> {
        // Advance the iterator while also returning the

        let curr_ch = self.curr_ch;
        let next_ch = self.contents.next();

        // Make the current 'look ahead' value the current value,
        // and set the newly retrieved value as the 'look ahead' value
        self.curr_ch = self.peek_ch;
        self.peek_ch = next_ch;

        return curr_ch;
    }

    pub fn lex(&mut self) -> Result<Vec<Token>, LexError> {
        let mut tokens = Vec::new();

        while let Some((ix, ch)) = self.curr_ch {
            match ch {
                ' ' | '\n' | '\t' => _ = self.next_char(),
                c => {
                    let tok = match c {
                        '0'..='9' => self.lex_numeric(),
                        'A'..='Z' | 'a'..='z' => self.lex_ident(),
                        x => return Err(LexError::UnknownToken((ix, x))),
                    }?;
                    tokens.push(tok);
                }
            };
        }
        return Ok(tokens);
    }

    pub fn lex_numeric(&mut self) -> Result<Token, LexError> {
        let mut acc = String::new();
        let mut is_float = false;

        while self.is_curr_char_numeric() {
            let (_, ch) = self
                .next_char()
                .expect("lex_numeric `should be pre-checked`");
            if ch == '.' {
                is_float = true
            };
            acc.push(ch);
        }

        match is_float {
            // Todo: add more numeric types (hence the pattern match)
            false => {
                let parsed_int =
                    acc.parse::<i32>().expect("lex_numeric `int conversion`");
                return Ok(Token::IntegerLiteral(parsed_int));
            }
            true => {
                let parsed_float = acc
                    .parse::<f32>()
                    .expect("lex_numeric `float conversion`");
                return Ok(Token::FloatLiteral(parsed_float));
            }
        }
    }

    pub fn lex_ident(&mut self) -> Result<Token, LexError> {
        let mut acc = String::new();
        while self.is_curr_char_part_of_ident() {
            let (_, ch) = self
                .next_char()
                .expect("lex_literal `already checked token`");
            acc.push(ch);
        }
        if let Some(keyword) = self.get_keyword(&acc) {
            return Ok(keyword);
        }
        return Ok(Token::Ident(acc));
    }

    pub fn get_keyword(&self, s: &String) -> Option<Token> {
        return Some(match s.as_str() {
            "return" => Token::RETURN,
            "if" => Token::IF,
            "else" => Token::ELSE,
            "for" => Token::FOR,
            "while" => Token::WHILE,
            _ => return None,
        });
    }

    pub fn is_curr_char_numeric(&self) -> bool {
        return match self.curr_ch {
            Some((_, ch)) if ch.is_numeric() || ch == '.' || ch == '_' => true,
            _ => false,
        };
    }

    pub fn is_curr_char_part_of_ident(&self) -> bool {
        return match self.curr_ch {
            Some((_, ch)) if ch.is_alphanumeric() || ch == '_' => true,
            _ => false,
        };
    }
}

#[test]
fn test_lexer_init() {
    let prg = "int";
    let l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));
    assert_eq!(l.curr_ch, Some((0, 'i')));
    assert_eq!(l.peek_ch, Some((1, 'n')));
}

#[test]
fn test_lexer_advance() {
    let prg = "int";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));
    // Should make n the curr char
    _ = l.next_char();
    assert_eq!(l.curr_ch, Some((1, 'n')));

    // Should make t the curr char
    _ = l.next_char();
    assert_eq!(l.curr_ch, Some((2, 't')));

    // Should make None the curr char
    _ = l.next_char();

    assert_eq!(l.curr_ch, None);
    assert_eq!(l.peek_ch, None);
}

#[test]
fn test_lexer_lex_ident() {
    let prg = "variablename";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let token = l.lex_ident();
    assert_eq!(token, Ok(Token::Ident(prg.to_string())));
}

#[test]
fn test_lexer_lex_ident_underscores() {
    let prg = "a_really_cool___variable_name";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let token = l.lex_ident();
    assert_eq!(token, Ok(Token::Ident(prg.to_string())));
}

#[test]
fn test_lexer_lex_ident_nums() {
    let prg = "a_variable_112313";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let token = l.lex_ident();
    assert_eq!(token, Ok(Token::Ident(prg.to_string())));
}

#[test]
fn test_lexer_lex_int() {
    let expected = 1012310293;
    let prg = format!("{}", expected);
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let token = l.lex_numeric();
    assert_eq!(token, Ok(Token::IntegerLiteral(expected)));
}

#[test]
fn test_lexer_lex_float() {
    let expected = 10123.10293;
    let prg = format!("{}", expected);
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let token = l.lex_numeric();
    assert_eq!(token, Ok(Token::FloatLiteral(expected)));
}

#[test]
fn test_lexer_lex_keywords() {
    let prg = "return if else while for";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let toks = l.lex();
    assert_eq!(
        toks,
        Ok(vec![
            Token::RETURN,
            Token::IF,
            Token::ELSE,
            Token::WHILE,
            Token::FOR
        ])
    );
}

#[test]
fn test_error_unknown_char() {
    let prg = "if|";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let should_be_err = l.lex();
    assert_eq!(should_be_err, Err(LexError::UnknownToken((2, '|'))));
}

#[test]
fn test_error_numeric_alpha() {
    let prg = "190ab";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let should_be_err = l.lex();
    assert_eq!(
        should_be_err,
        Err(LexError::InvalidIdentifier((
            "190ab".to_string(),
            InvalidIdentifierReason::StartsWithNumber
        )))
    );
}
