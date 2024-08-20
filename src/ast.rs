use std::fmt::{write, Display};

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
    IdentExpr(Token),
    BinaryOpExpr(BinOp),
    UnaryOpExpr(UnaryOp),
}

impl Expr {
    pub fn new(tk: Token) -> Option<Self> {
        return Some(match tk {
            Token::IntegerLiteral(_) => Expr::IntLiteral(tk.clone()),
            Token::Ident(_) => Expr::IdentExpr(tk.clone()),
            _ => return None,
        });
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::IdentExpr(Token::Ident(i)) => write!(f, "{}", i),
            Expr::BinaryOpExpr(BinOp { l, r, op }) => {
                write!(f, "{} {} {}", l, op, r)
            }
            Expr::UnaryOpExpr(UnaryOp { value, op }) => {
                write!(f, "{} {}", op, value)
            }
            Expr::IntLiteral(Token::IntegerLiteral(i)) => write!(f, "{}", i),
            _ => write!(f, "(NOT IMPLEMENTED)"),
        }
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
    pub expr: Expr,
}

#[derive(Debug, PartialEq)]
pub struct TypedIdent {}

#[derive(Debug, PartialEq)]
pub struct FnDef {
    pub type_: Token,
    pub name: Token,
    pub args: Vec<(Token, Token)>,
    pub body: Program,
}

impl Display for FnDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();
        buffer.push_str(format!("{} {}", self.type_, self.name).as_str());
        buffer.push_str("(");
        for (arg_type, arg_name) in &self.args {
            buffer.push_str(format!("{} {},", arg_type, arg_name).as_str());
        }
        buffer.push_str(")");
        buffer.push_str("{\n");
        for stmt in &self.body.statements {
            buffer.push_str(format!("\t{}\n", stmt).as_str());
        }
        buffer.push_str("}\n");

        write!(f, "{}", buffer)
    }

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
    FnDef(FnDef),
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Assign(AssignStmt { type_, name, value }) => {
                write!(f, "{} {} = {};", type_, name, value)
            }
            Statement::Return(ReturnStmt { expr }) => {
                write!(f, "return {};", expr)
            }
            Statement::FnDef(fn_def) => {
                write!(f, "{}", fn_def)
            }
            _ => write!(f, "(NOT IMPLEMENTED)"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();
        for s in &self.statements {
            buffer.push_str(format!("{}\n", s).as_str());
        }

        write!(f, "{}", buffer)
    }
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
            AstNode::Expr(expr) => write!(f, "{}", expr),
            AstNode::Program(prg) => write!(f, "{}", prg),
            AstNode::Statement(stmt) => write!(f, "{}", stmt),
            _ => write!(f, "NOT IMPLEMENTED"),
        }
    }
}
