use std::fmt::Display;

use crate::token::Token;

#[derive(Debug, PartialEq)]
pub struct BinOp {
    pub l: Box<Expr>,
    pub r: Box<Expr>,
    pub op: Token,
}

#[derive(Debug, PartialEq)]
pub struct UnaryOp {
    pub value: Box<Expr>,
    pub op: Token,
}

#[derive(Debug, PartialEq)]

pub enum Expr {
    IntLiteral(Token),
    BinaryOpExpr(BinOp),
    UnaryOpExpr(UnaryOp),
    // IntLiteral(Token)
}

impl Expr {
    pub fn new(tk: Token) -> Option<Self> {
        return Some(match tk {
            Token::IntegerLiteral(_) => Expr::IntLiteral(tk.clone()),
            _ => return None,
        });
    }
}

#[derive(Debug, PartialEq)]
pub struct AssignStmt {
    pub type_: Token,
    pub name: Token,
    pub value: Expr,
}

#[derive(Debug, PartialEq)]
pub struct ReturnStmt {
    pub expr: Expr
}

#[derive(Debug, PartialEq)]
pub struct ConditionalStmt {
    condition: Expr,
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Assign(AssignStmt),
    Conditional(ConditionalStmt),
    Return(ReturnStmt),
    Expr(Expr),
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Program(Program),
    Statement(Statement),
    Expr(Expr),
}

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            _ => write!(f, "NOT IMPLEMENTED"),
        }
    }
}
