use crate::{
    ast::{
        self, AssignStmt, AstNode, BinOp, Expr, Program, ReturnStmt,
        Statement, UnaryOp,
    },
    token::Token,
};

type TokIterItem = Token;

pub struct Parser<I>
where
    I: Iterator<Item = TokIterItem>,
{
    tokens: I,
    curr_token: Option<TokIterItem>,
    peek_token: Option<TokIterItem>,
}

#[derive(Debug, PartialEq)]
pub enum ParseError {
    Invalid(Option<Token>),
    InvalidStatementTerminator(Option<Token>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    Lowest,
    Eq,
    AddSub,
    MulDiv,
    Paren,
}

impl<I> Parser<I>
where
    I: Iterator<Item = TokIterItem>,
{
    pub fn new(tokens: I) -> Self {
        let mut p = Parser {
            tokens: tokens,
            curr_token: None,
            peek_token: None,
        };
        p.advance();
        p.advance();
        return p;
    }

    pub fn parse_program(&mut self) -> Result<AstNode, ParseError> {
        // Entry point

        let mut statements = Vec::new();
        while let Some(ref _tok) = self.curr_token {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }
        return Ok(AstNode::Program(Program {
            statements: statements,
        }));
    }

    pub fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        if let Some(tk) = &self.curr_token {
            let stmt = match tk {
                type_id if self.is_type_id(&type_id) => {
                    let type_ident = self
                        .consume_curr_tok()
                        .expect("parse_statement `should have pre-cheked type ident token`");
                    let assignment = self.parse_assignment(type_ident)?;
                    Statement::Assign(assignment)
                }
                Token::RETURN => {
                    self.advance();
                    Statement::Return(ReturnStmt {
                        expr: self.parse_expr(Precedence::Lowest)?,
                    })
                }
                _ => {
                    let expr = self.parse_expr(Precedence::Lowest)?;
                    Statement::Expr(expr)
                }
            };
            let terminator = self.consume_curr_tok();
            if !matches!(terminator, Some(Token::SEMICOLON)) {
                return Err(ParseError::InvalidStatementTerminator(
                    terminator,
                ));
            }
            return Ok(stmt);
        } else {
            return Err(ParseError::Invalid(None));
        }
    }

    pub fn parse_assignment(
        &mut self,
        type_ident: Token,
    ) -> Result<AssignStmt, ParseError> {
        match (&self.curr_token, &self.peek_token) {
            (Some(Token::Ident(_)), Some(Token::ASSIGN)) => {
                let name = self.consume_curr_tok().expect(
                    "parse_assignment `should have pre-checked name token`",
                );
                _ = self.consume_curr_tok();

                let expr = self.parse_expr(Precedence::Lowest)?;
                return Ok(AssignStmt {
                    type_: type_ident,
                    name: name,
                    value: expr,
                });
            }
            (a, b) => {
                println!("{:?} {:?}", &a, &b);
                let err_tok = self.consume_curr_tok();
                return Err(ParseError::Invalid(err_tok));
            }
        }
    }

    pub fn parse_expr(
        &mut self,
        precedence: Precedence,
    ) -> Result<Expr, ParseError> {
        while let Some(ref t) = self.curr_token {
            match t {
                Token::LPAREN => {
                    _ = self.consume_curr_tok();
                    // Parse what's inside the parens
                    let n = self.parse_expr(Precedence::Lowest)?;
                    return self.parse_expr_with(n, precedence);
                }
                op if self.is_maybe_unary_op(&op) => {
                    let op_ = self
                        .consume_curr_tok()
                        .expect("parse_expr `should have checked op token`");
                    let expr = self.parse_expr(Precedence::Lowest)?;
                    return Ok(Expr::UnaryOpExpr(UnaryOp {
                        value: Box::new(expr),
                        op: op_,
                    }));
                }
                Token::FloatLiteral(_) | Token::IntegerLiteral(_) => {
                    let lit = self.consume_curr_tok().expect("");
                    return self.parse_expr_with(
                        Expr::new(lit).expect(
                            "parse `literal should be valid expression`",
                        ),
                        precedence,
                    );
                }
                _ => {}
            }
            _ = self.consume_curr_tok();
        }
        return Err(ParseError::Invalid(None));
    }

    pub fn parse_expr_with(
        &mut self,
        captured_expr: Expr,
        precedence: Precedence,
    ) -> Result<Expr, ParseError> {
        if let Some(Token::SEMICOLON) = self.curr_token {
            return Ok(captured_expr);
        }
        Ok(match self.consume_curr_tok() {
            None => captured_expr,
            Some(Token::RPAREN) => return Ok(captured_expr),
            Some(tk) if self.is_binary_operator(&tk) => {
                let prec = self.get_precedence(&tk);
                if prec <= precedence {
                    return Ok(captured_expr);
                } else {
                    let r = self.parse_expr(prec)?;
                    return Ok(Expr::BinaryOpExpr(BinOp {
                        l: Box::new(captured_expr),
                        r: Box::new(r),
                        op: tk,
                    }));
                }
            }
            x @ Some(_) => return Err(ParseError::Invalid(x)),
        })
    }

    pub fn get_precedence(&self, tk: &Token) -> Precedence {
        return match tk {
            Token::EQ => Precedence::Eq,
            Token::ADD | Token::ADD_EQ => Precedence::AddSub,
            Token::STAR | Token::MUL_EQ => Precedence::MulDiv,
            Token::RPAREN => Precedence::Paren,
            _ => Precedence::Lowest,
        };
    }

    pub fn is_type_id(&self, tk: &Token) -> bool {
        match tk {
            Token::INT | Token::VOID | Token::CHAR => true,
            _ => false,
        }
    }

    pub fn is_maybe_unary_op(&self, tk: &Token) -> bool {
        return match tk {
            Token::NOT => true,
            _ => false,
        };
    }

    pub fn is_binary_operator(&self, tk: &Token) -> bool {
        match tk {
            Token::ADD | Token::STAR | Token::RPAREN | Token::EQ => true,
            _ => false,
        }
    }

    pub fn advance(&mut self) {
        /* Advances the token iterator without emitting the current token
        (Usually used where the token won't actually get moved/copied and
        has already been checked)
        */
        let _ = self.consume_curr_tok();
    }

    pub fn consume_curr_tok(&mut self) -> Option<TokIterItem> {
        let next_token = self.tokens.next();

        let curr_tok = self.curr_token.take();
        self.curr_token = self.peek_token.take();
        self.peek_token = next_token;
        return curr_tok;
    }
}

#[test]
fn test_parse_addition() {
    let mut p = Parser::new(
        vec![
            Token::IntegerLiteral(10),
            Token::ADD,
            Token::IntegerLiteral(10),
        ]
        .into_iter(),
    );

    let tree = p.parse_expr(Precedence::Lowest);
    assert_eq!(
        tree,
        Ok(Expr::BinaryOpExpr(BinOp {
            l: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
            r: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
            op: Token::ADD
        }))
    );
}

#[test]
fn test_assignment_stmt() {
    let mut p = Parser::new(
        vec![
            Token::INT,
            Token::Ident(String::from("i")),
            Token::ASSIGN,
            Token::IntegerLiteral(10),
            Token::SEMICOLON,
        ]
        .into_iter(),
    );
    let tree = p.parse_statement();

    assert_eq!(
        tree,
        Ok(Statement::Assign(AssignStmt {
            type_: Token::INT,
            name: Token::Ident(String::from("i")),
            value: Expr::IntLiteral(Token::IntegerLiteral(10))
        }))
    );
}

#[test]
fn test_parse_precedence() {
    let mut p = Parser::new(
        vec![
            Token::IntegerLiteral(10),
            Token::ADD,
            Token::IntegerLiteral(10),
            Token::STAR,
            Token::IntegerLiteral(20),
        ]
        .into_iter(),
    );

    let tree = p.parse_expr(Precedence::Lowest);

    let rhs = Expr::BinaryOpExpr(BinOp {
        l: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
        r: Box::new(Expr::IntLiteral(Token::IntegerLiteral(20))),
        op: Token::STAR,
    });
    let binary = Expr::BinaryOpExpr(BinOp {
        l: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
        r: Box::new(rhs),
        op: Token::ADD,
    });

    assert_eq!(tree, Ok(binary));
}

#[test]
fn test_parse_precedence_parens() {
    let mut p = Parser::new(
        vec![
            Token::LPAREN,
            Token::IntegerLiteral(10),
            Token::ADD,
            Token::IntegerLiteral(10),
            Token::RPAREN,
            Token::STAR,
            Token::IntegerLiteral(20),
        ]
        .into_iter(),
    );

    let tree = p.parse_expr(Precedence::Lowest);

    let lhs = Expr::BinaryOpExpr(BinOp {
        l: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
        r: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
        op: Token::ADD,
    });
    let binary = Expr::BinaryOpExpr(BinOp {
        l: Box::new(lhs),
        r: Box::new(Expr::IntLiteral(Token::IntegerLiteral(20))),
        op: Token::STAR,
    });

    assert_eq!(tree, Ok(binary));
}

#[test]
fn test_parse_unary() {
    let mut p = Parser::new(
        vec![
            Token::NOT,
            Token::IntegerLiteral(10),
            Token::EQ,
            Token::IntegerLiteral(10),
        ]
        .into_iter(),
    );

    let tree = p.parse_expr(Precedence::Lowest);

    let expr = Expr::BinaryOpExpr(BinOp {
        l: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
        r: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
        op: Token::EQ,
    });
    let unary_expr = Expr::UnaryOpExpr(UnaryOp {
        value: Box::new(expr),
        op: Token::NOT,
    });
    assert_eq!(tree, Ok(unary_expr));
}

#[test]
fn test_parse_return() {
    let mut p = Parser::new(
        vec![
            Token::RETURN,
            Token::IntegerLiteral(10),
            Token::ADD,
            Token::IntegerLiteral(10),
            Token::SEMICOLON,
        ]
        .into_iter(),
    );

    let tree = p.parse_statement();
    assert_eq!(
        tree,
        Ok(Statement::Return(ReturnStmt {
            expr: Expr::BinaryOpExpr(BinOp {
                l: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
                r: Box::new(Expr::IntLiteral(Token::IntegerLiteral(10))),
                op: Token::ADD,
            })
        }))
    );
}
