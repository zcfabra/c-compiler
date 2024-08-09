#[derive(Debug, PartialEq)]
pub enum Token {
    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,
    

    // Types 
    // INT(bool),
    // VOID(bool),
    // CHAR(bool),

    // Keywords
    RETURN,
    IF,
    ELSE,
    FOR,
    WHILE,

    // Literals
    Ident(String),
    IntegerLiteral(i32),
    FloatLiteral(f32),
}