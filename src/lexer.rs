use crate::token::{self, Token};
use std::fmt::Display;

#[derive(Debug, PartialEq, Eq)]
enum InvalidIdentifierReason {
    InvalidCharsFound(u32),
}

impl Display for InvalidIdentifierReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            Self::InvalidCharsFound(ix) => format!("Found Illegal Characters In Identifier: Invalids First Found At Position `{}`", ix),
        };
        write!(f, "{}", msg)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LexError {
    UnknownToken(IndexedCh),
    InvalidIdentifier((String, InvalidIdentifierReason)),
    InvalidNumeric((String, InvalidIdentifierReason)),
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
            Self::InvalidNumeric((str, reason)) => {
                format!("Invalid Numeric: `{}` - {}", str, reason)
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

pub fn is_terminator(c: char) -> bool {
    match c {
        ' ' | '\n' | '(' | '{' | '[' | ')' | '}' | ']' | ';' => true,
        _ => false,
    }
}

pub struct Lexer<I>
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
        let _ = l.consume_curr_char();
        let _ = l.consume_curr_char();
        return l;
    }

    pub fn consume_curr_char(&mut self) -> Option<IndexedCh> {
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
                ' ' | '\n' | '\t' => _ = self.consume_curr_char(),
                sc@('(' | ')' | '{' | '}' | '[' | ']' | ';') => {
                    tokens.push(self.get_single_char_token(sc, ix)?);
                }
                dc@('=' | '!' | '+' | '-' | '/' | '*') => {
                    let tok = match self.get_double_char_token(dc, ix) {
                        Some(tok) => Ok(tok),
                        None => self.get_single_char_token(ch, ix)
                    }?;
                    tokens.push(tok);
                }
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
        let mut err_found_at = None;

        while !self.is_curr_pattern_terminated() {
            let (ix, ch) = self
                .consume_curr_char()
                .expect("lex_numeric `should be pre-checked`");
            if ch == '.' {
                is_float = true
            };

            if !self.is_curr_char_part_of_numeric(ch) && err_found_at.is_none()
            {
                err_found_at = Some(ix);
            }

            acc.push(ch);
        }

        if let Some(err_ix) = err_found_at {
            return Err(LexError::InvalidNumeric((
                acc,
                InvalidIdentifierReason::InvalidCharsFound(err_ix),
            )));
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
        let mut err_started_at = None;

        while !self.is_curr_pattern_terminated() {
            let (ix, ch) = self
                .consume_curr_char()
                .expect("lex_ident `should have checked char`");

            if !self.is_part_of_ident(ch) && err_started_at.is_none() {
                err_started_at = Some(ix);
            }

            acc.push(ch);
        }

        if let Some(err_ix) = err_started_at {
            let reason = InvalidIdentifierReason::InvalidCharsFound(err_ix);
            return Err(LexError::InvalidIdentifier((acc, reason)));
        }

        return Ok(self.get_keyword(&acc).unwrap_or(Token::Ident(acc)));
    }

    pub fn get_single_char_token(&mut self, ch: char, ix: u32) -> Result<Token, LexError> {
        let tok = Ok(match ch {
            '(' => Token::LPAREN,
            ')' => Token::RPAREN,
            '{' => Token::LBRACE,
            '}' => Token::RBRACE,
            ';' => Token::SEMICOLON,

            '+' => Token::ADD,
            '-' => Token::SUB,
            '*' => Token::STAR,
            '/' => Token::DIV,

            '!' => Token::NOT,

            '=' => Token::ASSIGN,
            _ => return Err(LexError::UnknownToken((ix, ch)))
        });
        let _ = self.consume_curr_char();
        return tok;
    }

    pub fn get_double_char_token(&mut self, ch: char, ix: u32) -> Option<Token> {
        let tok = Some(match (ch, self.peek_ch) {
            ('=', Some((_, '='))) => Token::EQ,
            ('!', Some((_, '='))) => Token::NOT_EQ,
            ('+', Some((_, '='))) => Token::ADD_EQ,
            ('-', Some((_, '='))) => Token::SUB_EQ,
            ('*', Some((_, '='))) => Token::MUL_EQ,
            ('/', Some((_, '='))) => Token::DIV_EQ,
            (_, _) => return None
        });
        // Consumes current char
        _ = self.consume_curr_char();
        // Consumes next char
        _ = self.consume_curr_char();

        return tok;
        
    }

    pub fn get_keyword(&self, s: &String) -> Option<Token> {
        return Some(match s.as_str() {
            "return" => Token::RETURN,
            "if" => Token::IF,
            "else" => Token::ELSE,
            "for" => Token::FOR,
            "while" => Token::WHILE,

            // Types
            "int" => Token::INT,
            "void" => Token::VOID,
            "char" => Token::CHAR,

            _ => return None,
        });
    }

    pub fn is_curr_char_numeric(ch: char) -> bool {
        return ch.is_numeric() || ch == '.' || ch == '_';
    }

    pub fn is_curr_pattern_terminated(&self) -> bool {
        return match self.curr_ch {
            Some((_, ch)) if is_terminator(ch) => true,
            None => true,
            _ => false,
        };
    }

    pub fn is_curr_char_part_of_numeric(&self, ch: char) -> bool {
        return ch.is_numeric() || ch == '.' || ch == '_';
    }
    pub fn is_part_of_ident(&self, ch: char) -> bool {
        return ch.is_alphanumeric() || ch == '_';
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
    _ = l.consume_curr_char();
    assert_eq!(l.curr_ch, Some((1, 'n')));

    // Should make t the curr char
    _ = l.consume_curr_char();
    assert_eq!(l.curr_ch, Some((2, 't')));

    // Should make None the curr char
    _ = l.consume_curr_char();

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
    let prg = "name|";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let should_be_err = l.lex();
    assert_eq!(
        should_be_err,
        Err(LexError::InvalidIdentifier((
            prg.to_string(),
            InvalidIdentifierReason::InvalidCharsFound(4)
        )))
    );
}

#[test]
fn test_error_numeric_alpha() {
    let prg = "190ab";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let should_be_err = l.lex();
    assert_eq!(
        should_be_err,
        Err(LexError::InvalidNumeric((
            "190ab".to_string(),
            InvalidIdentifierReason::InvalidCharsFound(3)
        )))
    );
}

#[test]
fn test_if_else_parsing() {
    let prg = "if(condition) {int i = 10 + 10} else {int i = 0};";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let should_be_err = l.lex();
    assert_eq!(
        should_be_err,
        Ok(vec![
            Token::IF,
            Token::LPAREN,
            Token::Ident("condition".to_string()),
            Token::RPAREN,
            Token::LBRACE,
            Token::INT,
            Token::Ident("i".to_string()),
            Token::ASSIGN,
            Token::IntegerLiteral(10),
            Token::ADD,
            Token::IntegerLiteral(10),
            Token::RBRACE,
            Token::ELSE,
            Token::LBRACE,
            Token::INT,
            Token::Ident("i".to_string()),
            Token::ASSIGN,
            Token::IntegerLiteral(0),
            Token::RBRACE,
            Token::SEMICOLON,
        ])
    );
}

#[test]
fn test_operators() {

    let prg = "= == + += - -= ! != * *= / /=";
    let mut l = Lexer::new(prg.char_indices().map(|(ix, c)| (ix as u32, c)));

    let should_be_err = l.lex();
    assert_eq!(
        should_be_err,
        Ok(vec![
            Token::ASSIGN,
            Token::EQ,
            Token::ADD,
            Token::ADD_EQ,
            Token::SUB,
            Token::SUB_EQ,
            Token::NOT,
            Token::NOT_EQ,
            Token::STAR,
            Token::MUL_EQ,
            Token::DIV,
            Token::DIV_EQ,
        ])
    );
}