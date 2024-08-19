use std::fmt::Display;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,
    SEMICOLON,

    // Operators
    ASSIGN,
    EQ,

    ADD,
    ADD_EQ,

    SUB,
    SUB_EQ,

    NOT,
    NOT_EQ,
    

    // Not 'MUL' b/c of pointers
    STAR,
    MUL_EQ,

    DIV,
    DIV_EQ,

    // Types 
    POINTER,

    INT,
    VOID,
    CHAR,

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

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut repr;
        let display = match self {
            Self::ADD => "+",
            Self::IntegerLiteral(i) => {
                repr = format!("{}", i);
                repr.as_str()
            },
            _ => "NOT IMPLEMENTED"
        };
        write!(f, "{}", display)
    }
}

impl Token {
    pub fn make_ident(s: String) -> Token {
        return Token::Ident(s);
    }

}
