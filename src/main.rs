mod ast;
mod parser;

mod lexer;
mod token;

use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{Read, Write},
};

use lexer::Lexer;
use parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    if let Some(file_name) = args.get(1) {
        let mut f = fs::File::open(file_name).expect("SHOULD BE A FILE");
        let mut buffer: String = String::new();

        f.read_to_string(&mut buffer).expect("FAILED TO READ FILE");

        let tokens = Lexer::new(
            buffer
                .char_indices()
                .into_iter()
                .map(|(i, c)| (i as u32, c)),
        )
        .lex()
        .expect("TOKENIZER ERROR");

        println!("{:?}", tokens);

        let ast = Parser::new(tokens.into_iter())
            .parse()
            .expect("PARSE ERROR");

        println!("{}", ast);
    }
}
