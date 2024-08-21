use crate::{
    ast::{
        AstNode, BinOp, BlockStmt, Expr, FnDef, Program, ReturnStmt, Statement,
    },
    token::Token,
};

#[derive(Debug)]
pub enum CodeGenError {}

const NUM_SPACES: usize = 4;
pub struct Generator {
    pub output: String,
    indent: usize,
}

impl Generator {
    pub fn new() -> Self {
        let output = String::new();
        return Generator { output, indent: 0 };
    }

    pub fn get_asm(&self) -> String {
        return self.output.clone();
    }

    pub fn gen_asm(&mut self, node: &AstNode) -> Result<(), CodeGenError> {
        match node {
            AstNode::Program(Program { statements }) => {
                for stmt in statements {
                    self.gen_asm_statement(stmt)?;
                }
            }
            _ => {
                todo!()
            }
        };
        Ok(())
    }

    pub fn gen_asm_statement(
        &mut self,
        stmt: &Statement,
    ) -> Result<(), CodeGenError> {
        match stmt {
            Statement::FnDef(fn_def) => self.gen_asm_fn_def(fn_def),
            Statement::Return(rtrn) => self.gen_asm_return_statement(rtrn),
            _ => {
                todo!()
            }
        }
    }

    pub fn gen_asm_return_statement(
        &mut self,
        return_: &ReturnStmt,
    ) -> Result<(), CodeGenError> {
        self.gen_asm_expr(&return_.expr)?;
        self.push_line("ret");

        Ok(())
    }

    pub fn gen_asm_binary_expr(
        &mut self,
        bin_expr: &BinOp,
    ) -> Result<(), CodeGenError> {

        match bin_expr.op {
            Token::ADD => {
                self.gen_asm_expr(&*bin_expr.l)?;
                self.push_line("push %eax");
                self.gen_asm_expr(&*bin_expr.r)?;
                self.push_line("pop %ecx");
                self.push_line("addl %eax, %ecx");
            }
            _ => todo!()
        }

        Ok(())
    }

    pub fn gen_asm_expr(&mut self, expr: &Expr) -> Result<(), CodeGenError> {
        match expr {
            Expr::IntLiteral(Token::IntegerLiteral(intval)) => {
                self.push_line(format!("movl ${}, %eax", intval).as_str());
                Ok(())
            }
            Expr::BinaryOpExpr(bin_expr) => {
                self.gen_asm_binary_expr(bin_expr)
            }
            _ => {
                todo!()
            }
        }
    }

    pub fn gen_asm_block_statement(
        &mut self,
        block: &BlockStmt,
    ) -> Result<(), CodeGenError> {
        for stmt in &block.statements {
            self.gen_asm_statement(&stmt)?;
        }

        Ok(())
    }
    pub fn gen_asm_fn_def(
        &mut self,
        fn_def: &FnDef,
    ) -> Result<(), CodeGenError> {
        self.push_line(format!(".globl {}", fn_def.name).as_str());
        self.push_line(format!("{}:", fn_def.name).as_str());
        self.incr_indent();
        self.gen_asm_block_statement(&fn_def.body)?;

        Ok(())
    }

    pub fn incr_indent(&mut self) {
        self.indent += 1;
    }

    pub fn decr_indent(&mut self) {
        self.indent -= 1;
    }
    pub fn push_line(&mut self, str: &str) {
        let spaces = " ".repeat(NUM_SPACES * self.indent);
        self.output
            .push_str(format!("{}{}\n", spaces, str).as_str());
    }
}
