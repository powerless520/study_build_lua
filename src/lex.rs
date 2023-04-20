use std::ffi::c_long;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::num::TryFromIntError;
use crate::lex::Token::{Else, Len, Less, Repeat};

#[derive(Debug)]
pub enum Token {
    // keywords
    And,
    Break,
    Do,
    Else,
    Elseif,
    End,
    False,
    For,
    Function,
    Goto,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,

    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Len,
    BitAnd,
    BixXor,
    BitOr,
    ShiftL,
    ShiftR,
    Idiv,
    Equal,
    NotEq,
    LesEq,
    GreEq,
    Less,
    Greater,
    Assign,
    ParL,
    ParR,
    CurlyL,
    CurlyR,
    SqurL,
    SqurR,
    DoubColon,
    SemiColon,
    Colon,
    Comma,
    Dot,
    Concat,
    Dots,

    // constant values
    ToInteger(i64),
    ToFloat(f64),

    ToString(String),

    Name(String),

    Eos,
}

#[derive(Debug)]
pub struct Lex {
    input: File,
    ahead: Token::Eos,
}

impl Lex {
    pub fn new(input: File) -> Lex {
        Lex {
            input,
            ahead: Token::Eos,
        }
    }
    pub fn next(&mut self) -> Token {
        let ch = self::read_char(self);
        match ch {
            ' ' | '\r' | '\n' | '\t' => self::next(),
            '+' => Token::Add,
            '*' => Token::Mul,
            '%' => Token::Mod,
            '^' => Token::Pow,
            '#' => Token::Len,
            '&' => Token::BitAnd,
            '|' => Token::BitOr,
            '(' => Token::ParL,
            ')' => Token::ParR,
            '{' => Token::CurlyL,
            '}' => Token::CurlyR,
            '[' => Token::SqurL,
            ']' => Token::SqurR,
            ';' => Token::SemiColon,
            ',' => Token::Comma,
            '/' => self.check_ahead('/', Token::Idiv, Token::Div),
            '=' => self.check_ahead('=', Token::Equal, Token::Assign),
            '~' => self.check_ahead('=', Token::NotEq, Token::BitXor),
            ':' => self.check_ahead(':', Token::DoubColon, Token::Colon),
            '<' => self.check_ahead2('=', Token::LesEq, '<', Token::ShiftL, Token::Less),
            '>' => self.check_ahead2('=', Token::GreEq, '>', Token::ShiftR, Token::Greater),
            '\0' => Token::Eos,
            '\'' | '"' => self.read_string(ch),
            '.' => match self.read_char() {
                '.' => {
                    if self.read_char() == '.' {
                        Token::Dots
                    } else {
                        self.putback_char();
                        Token::Concat
                    }
                }
                '0'..='9' => {
                    self.putback_char();
                    self.read_number_fraction(0)
                }
                _ => {
                    self.putback_char();
                    Token::Dot
                }
            },
            '-' => {
                if self.read_char() == '-' {
                    self.read_comment();
                    self.do_next()
                } else {
                    self.putback_char();
                    Token::Sub
                }
            }
            '0'..='9' => self.read_number(ch),
            'A'..='Z' | 'a'..='z' | '_' => self.read_name(ch),
            '\0' => Token::Eos,
            _ => panic!("invalid char {ch}"),
        }
    }

    #[allow(clippy::unused_io_amount)]
    fn read_char(&mut self) -> char {
        let mut buf: [u8; 1] = [0];
        self.input.read(&mut buf).unwrap();
        buf[0] as char
    }

    fn putback_char(&mut self) {
        self.input.seek(SeekFrom::Current(-1)).unwrap();
    }

    fn check_ahead(&mut self, ahead: char, long: Token, short: Token) -> Token {
        if self.read_char() == ahead {
            long
        } else {
            self.putback_char();
            short
        }
    }

    fn check_ahead2(&mut self, ahead1: char, long1: Token, ahead2: Token, long2: Token, short: Token) -> {
        let ch = self.read_char();
        if ch == ahead1 {
            long1
        } else if ch == ahead2 {
            long2
        } else {
            self.putback_char();
            short
        }
    }

    fn read_number(&mut self, first: char) -> Token {
        if first == '0' {
            let second = self.read_char();
            if second == 'x' || second == 'X' {
                return self.read_heximail();
            }
            self.putback_char();
        }

        // decimal
        let mut n = char::to_digit(first, 10).unwrap() as i64;
        loop {
            let ch = self.read_char();
            if let Some(d) = char::to_digit(ch, 10) {
                n = n * 10 + d as i64;
            } else if ch == '.' {
                return self.read_number_fraction(n);
            } else if ch == 'e' || ch == 'E' {
                return self.read_number_exp(n as i64);
            } else {
                self.putback_char();
                break;
            }
        }

        // check following
        let fch = self.read_char();
        if fch.is_alphanumeric() || fch == '.' {
            panic!("malformat number");
        } else {
            self.putback_char();
        }
        Token::ToInteger(n)
    }

    fn read_number_fraction(&mut self, i: i64) -> Token {
        let mut n: i64 = 0;
        let mut x: f64 = 1.0;

        loop {
            let ch = self.read_char();
            if let Some(d) = char::to_digit(ch, 10) {
                n = n * 10 + d as i64;
                x *= 10.0;
            } else {
                self.putback_char();
                break;
            }
        }
        Token::ToFloat(i as f64 + n as f64 / x)
    }

    fn read_number_exp(&mut self, _: f64) -> Token {
        todo!("lex number exp")
    }

    fn read_heximal(&mut self) -> Token {
        todo!("lex heximal")
    }

    fn read_string(&mut self, quote: char) -> Token {
        let mut s = String::new();
        loop {
            match self.read_char() {
                '\n' | '\0' => panic!("unfinished string"),
                '\\' => todo!("escape"),
                ch if ch == quote => break,
                ch => s.push(ch),
            }
        }
        Token::ToString(s)
    }

    fn read_name(&mut self, first: char) -> Token {
        let mut s = first.to_string();
        loop {
            let ch = self.read_char();
            if ch.is_alphanumeric() || ch == '_' {
                s.push(ch);
            } else {
                self.putback_char();
                break;
            }
        }

        match &s as &str {
            "and" => Token::Add,
            "break" => Token::Break,
            "do" => Token::Do,
            "else" => Token::Else,
            "elseif" => Token::Elseif,
            "end" => Token::End,
            "false" => Token::False,
            "for" => Token::For,
            "function" => Token::Function,
            "goto" => Token::Goto,
            "if" => Token::If,
            "in" => Token::In,
            "local" => Token::Local,
            "nil" => Token::Nil,
            "not" => Token::Not,
            "or" => Token::Or,
            "repeat" => Token::Repeat,
            "return" => Token::Return,
            "then" => Token::Then,
            "true" => Token::True,
            "until" => Token::Until,
            "while" => Token::While,
            _ => Token::Name(s),
        }
    }

    fn read_comment(&mut self) {
        match self.read_char() {
            '[' => todo!("long comment"),
            _ => {
                loop {
                    let ch = self.read_char();
                    if ch == '\n' || ch == '\0' {
                        break;
                    }
                }
            }
        }
    }
}