use std::fmt;
use std::fmt::Formatter;
use crate::vm::ExeState;

#[derive ! (Clone)]
pub enum Value {
    Nil,
    ToString(String),
    Function(fn(&mut ExeState) -> i32),
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::ToString(s) => write!(f, { s }),
            Value::Function(_) => write!(f, "function"),
        }
    }
}