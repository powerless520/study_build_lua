use std::cmp::Ordering;
use std::collections::HashMap;
use std::io::Seek;
use crate::bytecode::ByteCode;
use crate::value::Value;
use crate::parse::ParseProto;

// It supports only 1 argument and assumes the argument is at index:1 on stack.
fn lib_print(state:&mut ExeState) -> i32{
    println!("{:?}",state.stack([1]));
    0
}

pub struct ExeState{
    globals:HashMap<String,Value>,
    stack:Vec<Value>,
}