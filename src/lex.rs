use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

#[derive(Debug)]
pub enum Token {
    Name(String),
    ToString(String),
    Eos,
}

#[derive(Debug)]
pub struct Lex {
    input: File,
}

impl Lex {
    pub fn new(input: File) -> Lex {
        Lex {
            input,
        }
    }
    pub fn next(&mut self) -> Token {
        let ch = self::read_char(self);
        match ch {
            ' ' | '\r' | '\n' | '\t' => self::next(),
            '\0' => Token::Eos,
            '"' => {
                let mut s = String::new();
                loop {
                    match self.read_char() {
                        '\0' => panic!("unfinsihed literal string"),
                        '"' => break,
                        ch => s.push(ch)
                    }
                }
                Token::ToString(s)
            }
            'A'..='Z' | 'a'..='z' | '_' => {
                let mut name = String::new();
                name.push(ch);
                loop {
                    match self.read_char() {
                        '\0' => break,
                        '_' => name.push('_'),
                        ch if ch.is_alphanumeric() => name.push(ch),
                        _ => {
                            self.input.seek(SeekFrom::Current(-1)).unwrap();
                            break;
                        }
                    }
                }
                Token::Name(name)
            }
            _ => panic!("unexpeceted char:{}", ch)
        }
    }

    fn read_char(&mut self) -> char {
        let mut buf: [u8; 1] = [0; 1];
        if self.input.read(&mut buf).unwrap() == 1 {
            buf[0] as char
        } else {
            '\0'
        }
    }
}