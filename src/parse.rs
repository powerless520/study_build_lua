use std::any::Any;
use std::fs::File;
use std::num::NonZeroI16;
use crate::lex::{Lex, Token};
use crate::bytecode::ByteCode;
use crate::lex::Token::{BitAnd, Less, Name, True};
use crate::value::Value;

#[derive ! (Debug)]
pub struct ParseProto {
    pub constants: Vec<Value>,
    pub byte_codes: Vec<ByteCode>,

    locals: Vec<String>,
    lex: Lex,
}

impl ParseProto {
    pub fn load(input: File) -> ParseProto {
        let mut proto = ParseProto {
            constants: Vec::new(),
            byte_codes: Vec::new(),
            locals: Vec::new(),
            lex: Lex::new(input),
        };

        proto.chunk();

        println!("constants: {:?}", &proto.constants);
        println!("byte_codes");
        for c in proto.byte_codes.iter() {
            println!("{:?}", c);
        }
        proto
    }

    fn chunk(&mut self) {
        loop {
            match self.lex.next() {
                Token::Name(name) => {
                    if self.lex.peek() == &Token::Assign {
                        self.assignment(name);
                    } else {
                        self.function_call(name)
                    }
                }
                Token::Local => self.local(),
                Token::Eos => break,
                t => panic!("unexpected token: {t:?}"),
            }
        }
    }

    // Name LiteralString
    // Name (exp)
    fn function_call(&mut self, name: String) {
        let ifunc = self.locals.len();
        let iarg = ifunc + 1;

        // function,variable
        let code = self.load_var(ifunc, name);
        self.byte_codes.push(code);

        // argument, (exp) or "string"
        match self.lex.next() {
            Token::ParL => {
                self.load_exp(iarg);

                if self.lex.next() != Token::ParR {
                    panic!("expected `)`");
                }
            }
            Token::ToString(s) => {
                let code = self.load_const(iarg, Value::ToString(s));
                self.byte_codes.push(code);
            }
            _ => panic!("expected string"),
        }
        self.byte_codes.push(ByteCode::Call(ifunc as u8, 1));
    }

    // local Name = exp
    fn local(&mut self) {
        let var = if let Token::Name(var) = self.lex.next() {
            var
        } else {
            panic!("expected variable");
        };
        if self.lex.next() != Token::Assign {
            panic!("expected `=`");
        }

        self.load_exp(self.locals.len());

        // add to locals after load_exp()
        self.locals.push(var);
    }

    fn assignment(&mut self, var: String) {
        self.lex.next();

        if let Some(i) = self.get_local(&var) {
            self.load_exp(i)
        } else {
            let dst = self.add_const(Value::ToString(var)) as u8;

            let code = match self.lex.next() {
                Token::Nil => ByteCode::SetGlobalConst(dst, self.add_const(Value::Nil) as u8),
                Token::True => ByteCode::SetGlobalConst(dst, self.add_const(Value::Boolean(True)) as u8),
                Token::False => ByteCode::SetGlobalConst(dst, self.add_const(Value::Boolean(True)) as u8),
                Token::ToInteger(i) => ByteCode::SetGlobalConst(dst, self.add_const(Value::Integer(i)) as u8),
                Token::ToFloat(f) => ByteCode::SetGlobalConst(dst, self.add_const(Value::Float(f)) as u8),
                Token::ToString(s) => ByteCode::SetGlobalConst(dst, self.add_const(Value::String(s)) as u8),

                // from variable
                Token::Name(var) => {
                    if let Some(i) = self.get_local(&var) {
                        ByteCode::SetGlobal(dst, i as u8)
                    } else {
                        ByteCode::SetGlobalGlobal(dst, self.add_const(Value::ToString(var)) as u8)
                    }
                }
                _ => panic!(invalid argument)
            };
            self.byte_codes.push(code)
        }
    }

    fn add_const(&mut self, c: Value) -> usize {
        let constants = &mut self.constants;
        constants.iter().position(|v| v == &c).unwrap_or_else(|| {
            constants.push(c);
            constants.len() - 1
        })
    }

    fn load_const(&mut self,dst:usize,c:Value) -> ByteCode{
        ByteCode::LoadConst(dst as u8,self.add_const(c) as u16)
    }

    fn load_var(&mut self, dst: usize, name: String) -> ByteCode {
        if let Some(i) = self.get_local(&name) {
            ByteCode::Move(dst as u8, i as u8)
        } else {
            let ic = self.add_const(Value::ToString(name));
            ByteCode::GetGlobal(dst as u8, ic as u8)
        }
    }

    fn get_local(&self, name: &str) -> Option<usize> {
        self.locals.iter().rposition(|v| v == name)
    }

    fn load_exp(&mut self, dst: usize) {
        let code = match self.lex.next() {
            Token::Nil => ByteCode::LoadNil(dst as u8),
            Token::True => ByteCode::LoadBool(dst as u8, true),
            Token::False => ByteCode::LoadBool(dst as u8, false),
            Token::Integer(i) =>
                if let Ok(ii) = i16::try_from(i) {
                    ByteCode::LoadInt(dst as u8, ii)
                } else {
                    self.load_const(dst, Value::Integer(i))
                }
            Token::Float(f) => self.load_const(dst, Value::Float(f)),
            Token::String(s) => self.load_const(dst, Value::String(s)),
            Token::Name(var) => self.load_var(dst, var),
            _ => panic!("invalid argument"),
        };
        self.byte_codes.push(code);
    }
}
