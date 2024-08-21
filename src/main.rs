mod ast;
mod parser;
mod codegen;

mod lexer;
mod token;


use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{Read, Write},
};

use codegen::Generator;
use lexer::make_lexer;
use parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    if let Some(file_name) = args.get(1) {
        let mut f = fs::File::open(file_name).expect("SHOULD BE A FILE");
        let mut buffer: String = String::new();

        f.read_to_string(&mut buffer).expect("FAILED TO READ FILE");

        let tokens = 
        make_lexer(&buffer)
        .lex()
        .expect("TOKENIZER ERROR");

        // println!("{:?}", tokens);

        let ast = Parser::new(tokens.into_iter())
            .parse()
            .expect("PARSE ERROR");

        println!("{}", ast);

        let mut generated = Generator::new();
        generated.gen_asm(&ast).expect("CODEGEN ERROR");
        let mut f = fs::File::create("out.s").expect("FILE WRITE ERR");
        println!("{}", &generated.output);
        f.write(generated.output.as_bytes());
    }
}
