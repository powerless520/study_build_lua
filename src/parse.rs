use std::fs::File;
use crate::lex::{Lex, Token};
use crate::bytecode::ByteCode;
use crate::value::Value;

#[derive ! (Debug)]
pub struct ParseProto {
    pub constants: Vec<Value>,
    pub byte_codes: Vec<ByteCode>,
}

pub fn load(input: File) -> ParseProto {
    let mut constants = Vec::new();
    let mut byte_codes = Vec::new();
    let mut lex = Lex::new(input);

    loop {
        match lex.next() {
            Token::Name(name) => {
                constants.push(Value::ToString(name));
                byte_codes.push(ByteCode::LoadConst(0, (constants.len() - 1) as u8));
                if let Token::ToString(s) = lex.next() {
                    constants.push(Value::ToString(s));
                    byte_codes.push(ByteCode::LoadConst(1, (constants.len() - 1) as u8));
                    byte_codes.push(ByteCode::Call(0, 1));
                } else {
                    panic!("expected string")
                }
            }
            Token::Eos => break,
            t => panic!("unexpected token: {t:?}"),
        }
    }

    dbg!(&constants);
    dbg!(&byte_codes);
    ParseProto { constants, byte_codes }
}