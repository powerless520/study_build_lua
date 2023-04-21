use std::any::Any;
use std::cmp::Ordering;
use std::env::var;
use std::fs::File;
use std::io::Read;
use std::iter::FlatMap;
use std::num::NonZeroI16;
use std::rc::Rc;
use crate::lex::{Lex, Token};
use crate::bytecode::ByteCode;
use crate::lex::Token::{BitAnd, False, Less, Name, True};
use crate::value::Value;

type FnBc2u8 = fn(u8, u8) -> ByteCode;
type FnBc3u8 = fn(u8, u8, u8) -> ByteCode;
type FnBcBool = fn(u8, u8, u8) -> ByteCode;

#[derive(Debug, PartialEq)]
enum ExpDesc {
    // constants
    Nil,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(Vec<u8>),

    // variables
    Local(usize),
    // including temprary variables on stack
    UpValue(usize),

    // table index
    Index(usize, usize),
    IndexField(usize, usize),
    IndexInt(usize, u8),
    IndexUpField(usize, usize), // covers global variables

    // function call
    Function(usize),
    Closure(usize),
    Call(usize, usize),
    VarArgs,

    // arithmetic
    UpAryOp(FnBc2u8, usize),
    // (opcode,operand)
    BinaryOp(FnBc3u8, usize, usize), // (opcode,left-operand,right-operand)

    // binaray logical operators: 'and', 'or'
    Test(Box<ExpDesc>, Vec<usize>, Vec<usize>), // (condition,true-list,false-list)

    // relational operators, e.g. '==','<=='
    Compare(FnBcBool, usize, usize, Vec<usize>, Vec<usize>),
}

enum ConstStack {
    Const(usize),
    Stack(usize),
}

#[derive(Debug)]
struct GoToLabel {
    name: String,
    icode: usize,
    nvar: usize,
}

// index of locals/upvalues in upper functions
#[derive(Debug)]
pub enum UpIndex {
    Local(usize),
    UpValue(usize),
}

#[derive(Debug, Default)]
pub struct FuncProto {
    pub has_varargs: bool,
    pub nparam: usize,
    pub constants: Vec<Value>,
    pub upindexes: Vec<UpIndex>,
    pub byte_codes: Vec<ByteCode>,
}

#[derive(Debug, Default)]
struct Level {
    locals: Vec<(String, bool)>,
    // (name,refered-as-upvalue)
    upvalues: Vec<(String, UpIndex)>,
}

#[derive(Debug)]
struct ParseContext<R: Read> {
    levels: Vec<Level>,
    lex: Lex<R>,
}

#[derive(Debug)]
struct ParseProto<'a, R: Read> {
    // return to VM to execute
    fp: FuncProto,

    // internal stuff for parsing
    sp: usize,
    breal_blocks: Vec<Vec<usize>>,
    continue_blocks: Vec<Vec<(usize, usize)>>,
    gotos: Vec<GoToLabel>,
    labels: Vec<GoToLabel>,
    ctx: &'a mut ParseContext<R>,
}

impl<'a, R: Read> ParseProto<'a, R> {
    fn block(&mut self) -> Token {
        let nvar = self.local_num();
        let end_token = self.block_scope();
        self.local_expire(nvar);
        end_token
    }

    fn block_scope(&mut self) -> Token {
        let igoto = self.gotos.len();
        let ilabel = self.labels.len();

        loop {
            // reset  sp before each statement
            self.sp = self.local_num();

            match self.ctx.lex.next() {
                Token::SemiColon => (),
                t @ Token::Name(_) | t @ Token::ParL => {
                    // this is not standard@
                    if self.try_continue_stat(&t) {
                        continue;
                    }

                    // functioncall and var-assignment both begin with `prefixexp` which begins with `Name` or `(`.
                    let desc = self.prefixexp(t);
                    if let ExpDesc::Call(ifunc, narg_plus) = desc {
                        // prefixexp() matches the whole functioncall statement.
                        let code = ByteCode::Call(ifunc as u8, narg_plus as u8, 0);
                        self.fp.byte_codes.push(code);
                    } else {
                        // prefoxexp() mactches only the first variable,so we continue the statement
                        self.assignment(desc)
                    }
                }
                Token::Local => {
                    if self.ctx.lex.peek() == &Token::Function {
                        self.local_function()
                    } else {
                        self.local_variables()
                    }
                }
                Token::Function => self.function_stat(),
                Token::If => self.if_stat(),
                Token::While => self.while_stat(),
                Token::Repeat => self.repeat_stat(),
                Token::For => self.for_stat(),
                Token::Break => self.break_stat(),
                Token::Do => self.do_stat(),
                Token::DoubColon => self.label_stat(),
                Token::Goto => self.goto_stat(),
                Token::Return => self.ret_stat(),
                t => {
                    self.labels.truncate(ilabel);
                    break t;
                }
            }
        }
    }

    fn local_variables(&mut self) {
        // variables names
        let mut vars = vec![self.read_name()];
        while self.ctx.lex.peek() == &Token::Comma {
            self.ctx.lex.next();
            vars.push(self.read_name());
        }

        if self.ctx.lex.peek() == &Token::Assign {
            // explist
            self.ctx.lex.next();
            self.explist_want(vars.len());
        } else {
            // no exp,load nils
            let code = ByteCode::LoadNil(self.sp as u8, vars.len() as u8);
            self.fp.byte_codes.push(code);
        }

        // append vars into self.locals after evaluating explist
        for var in vars.into_iter() {
            self.loval_new(var);
        }
    }

    fn local_function(&mut self) {
        self.ctx.lex.next();
        let name = self.read_name();
        println!("== function: {name}");

        // create `name` local variable before parsing funcbody(),
        // so the function can be called in body as recursion.
        self.local_new(name);

        let f = self.funcbody(false);
        self.discharge(self.sp, f);
    }

    fn function_stat(&mut self) {
        let name = self.read_name();
        let mut desc = self.simple_name(name);

        let with_self = loop {
            match self.ctx.lex.peek() {
                Token::Dot => {
                    self.ctx.lex.next();
                    let name = self.read_name();
                    let t = self.discharge_any(desc);
                    desc = ExpDesc::IndexField(t, self.add_const(name));
                }
                Token::Colon => {
                    self.ctx.lex.next();
                    let name = self.read_name();
                    let t = self.discharge_any(desc);
                    desc = ExpDesc::IndexField(t, self.add_const(name));
                }
                _ => break false
            }
        };

        let body = self.funcbody(with_self);
        self.assign_var(desc, body);
    }

    fn funcbody(&mut self, with_self: bool) -> ExpDesc {
        // paramter list
        let mut has_varargs = false;
        let mut params = Vec::new();
        if with_self {
            params.push(String::from("self"));
        }
        self.ctx.lex.expect(Token::ParL);
        loop {
            match self.ctx.lex.next() {
                Token::Name(name) => {
                    params.push(name);
                    match self.ctx.lex.next() {
                        Token::Comma => (),
                        Token::ParR => break,
                        t => panic!("invalid parameter {t:?}"),
                    }
                }
                Token::Dots => {
                    has_varargs = true;
                    self.ctx.lex.expect(Token::ParR);
                    break;
                }
                Token::ParR => break,
                t => panic!("invalid paramter {t:?}")
            }
        }
        let proto = chunk(self.ctx, has_varargs, params, Token::End);

        let no_upvalue = proto.upindexes.is_empty();
        let iconst = self.add_const(Value::LuaFunction(Rc::new(proto)));
        if no_upvalue {
            ExpDesc::Function(iconst)
        } else {
            ExpDesc::Closure(iconst)
        }
    }

    fn assignment(&mut self, first_var: ExpDesc) {
        // read varlist into @vars
        let mut vars = vec![first_var];
        loop {
            match self.ctx.lex.next() {
                Token::Comma => {
                    let token = self.ctx.lex.next();
                    vars.push(self.prefixexp(token));
                }
                Token::Assign => break,
                t => panic!("invalid assign {t:?}"),
            }
        }

        let sp0 = self.sp;
        let (mut nexp, last_exp) = self.explist();

        // assignment last variable
        match (nexp + 1).cmp(&vars.len()) {
            Ordering::Equal => {
                // assign last variable directly to avoid potential discharging
                let last_var = vars.pop().unwrap();
                self.assign_var(last_var, last_exp);
            }
            Ordering::Less => {
                // expand last expressions
                self.discharge_expand_want(last_exp, vars.len() - nexp);
                nexp = vars.len();
            }
            Ordering::Greater => {
                // drop extra exps
                nexp = vars.len();
            }
        }
        while let Some(var) = vars.pop() {
            nexp -= 1;
            self.assign_from_stack(var, sp0 + nexp);
        }
    }

    fn if_stat(&mut self) {
        let mut jmp_ends = Vec::new();

        let mut end_token = self.do_if_block(&mut jmp_ends);

        while end_token == Token::Elseif {
            end_token = self.do_if_block(&mut jmp_ends);
        }

        if end_token == Token::Else {
            end_token = self.block();
        }

        assert_eq!(end_token, Token::End);

        let iend = self.fp.byte_codes.len() - 1;
        for i in jmp_ends.into_iter() {
            self.fp.byte_codes[i] = ByteCode::Jump((iend - i) as i16)
        }
    }

    fn do_if_block(&mut self, jmp_ends: &mut Vec<usize>) -> Token {
        let condition = self.exp();
        let false_list = self.test_or_jump(condition);

        self.ctx.lex.expect(Token::Then);

        let end_token = self.block();

        if matches!(end_token,Token::Elseif | Token::Else) {
            self.fp.byte_codes.push(ByteCode::Jump(0));
            jmp_ends.push(self.fp.byte_codes.len() - 1);
        }

        self.fix_test_list(false_list);

        end_token
    }


    fn while_stat(&mut self) {
        let istart = self.fp.byte_codes.len();

        let condition = self.exp();
        let false_list = self.test_or_jump(condition);

        self.ctx.lex.expect(Token::Do);

        self.push_loop_block();

        assert_eq!(self.block(), Token::End);

        let iend = self.fp.byte_codes.len();
        self.fp.byte_codes.push(ByteCode::Jump(-(iend - istart) as i16) - 1);

        self.pop_loop_block(istart);

        self.fix_test_list(false_list);
    }


    fn repeat_stat(&mut self) {
        let istart = self.fp.byte_codes.len();

        self.push_loop_block();

        let nvar = self.local_num();

        assert_eq!(self.block_scope(), Token::Until);
        let iend = self.fp.byte_codes.len();

        let condition = self.exp();
        let false_list = self.test_or_jump(condition);
        self.fix_test_list_to(false_list, istart);

        self.pop_loop_block(iend);

        // expire internal local variables after reading condition exp and pop_loop_block()
        self.local_expire(nvar);
    }

    fn for_stat(&mut self) {
        let name = self.read_name();
        if self.ctx.lex.peek() == &Token::Assign {
            self.numberical_for(name);
        } else {
            self.generic_for(name);
        }
    }

    fn numerical_for(&mut self, name: String) {
        self.ctx.lex.next();

        let (nexp, last_exp) = self.explist();
        self.discharge(self.sp, last_exp);

        match nexp + 1 {
            2 => self.discharge(self.sp, ExpDesc::Integer(1)),
            3 => (),
            _ => panic!("invalid numerical for exp"),
        }

        // create 3 local variables: the first it iterator,
        // and the other two to keep stack positions.
        self.loca_new(name);
        self.loca_new(String::from(""));
        self.local_new(String::from(""));

        self.ctx.lex.expect(Token::Do);

        self.fp.byte_codes.push(ByteCode::ForPrepare(0, 0));
        let iprepare = self.fp.byte_codes.len() - 1;
        let iname = self.sp - 3;

        self.push_loop_block();

        assert_eq!(self.block(), Token::End);

        self.local_expire(self.local_num() - 3);

        let d = self.fp.byte_codes.len() - iprepare;
        self.fp.byte_codes.push(ByteCode::ForLoop(iname as u8, d as u16));
        self.fp.byte_codes[iprepare] = ByteCode::ForPrepare(iname as u8, d as u16);

        self.pop_loop_block(self.fp.byte_codes.len() - 1);
    }

    fn generic_for(&mut self, name: String) {
        let mut vars = vec![name];
        loop {
            match self.ctx.lex.next() {
                Token::Comma => continue,
                Token::In => break;
                Token::Name(name) => vars.push(name),
                _ => panic!("invalid generic_for namelist"),
            }
        }

        // explist
        let iter = self.sp;
        self.explist_want(3);

        let nvar = vars.len();
        self.local_new(String::from("")); // iterator function
        self.local_new(String::from("")); // immutable state
        self.local_new(String::from("")); // control variable
        for var in vars.into_iter() {
            self.local_new(var)
        }

        self.ctx.lex.expect(Token::Do);

        // jump to ByteCode::ForCallLoop at end of block
        self.fp.byte_codes.push(ByteCode::Jump(0));
        let ijump = self.fp.byte_codes.len() - 1;

        self.push_loop_block();

        // parse block!
        assert_eq!(self.block(), Token::End);

        // expire local variables above,before ByteCode::Jump
        self.local_expire(self.local_num() - 3 - nvar);

        let d = self.fp.byte_codes.len() - ijump;
        self.fp.byte_codes[ijump] = ByteCode::Jump(d as i16 - 1);
        if let Ok(d) = u8::try_from(d) {
            self.fp.byte_codes.push(ByteCode::ForCallLoop(iter as u8, nvar as u8, d as u8));
        } else {
            self.fp.byte_codes.push(ByteCode::ForCallLoop(iter as u8, nvar as u8, 0));
            self.fp.byte_codes.push(ByteCode::Jump(-(d as i16) - 1));
        }

        self.pop_loop_block(self.fp.byte_codes.len() - 1)
    }

    fn break_stat(&mut self) {
        let Some(breaks) = self.breal_blocks.last_mut() else {
            panic!("break outside loop");
        };
        self.fp.byte_codes.push(ByteCode::Jump(0));
        breaks.push(self.fp.byte_codes.len() - 1);
    }

    fn try_continue_stat(&mut self, name: &Token) -> bool {
        let Token::Name(name) = name else {
            return false;
        };
        if !matches!(self.ctx.lex.peek(),Token::End|Token::Elseif|Token::Else) {
            return false;
        }

        let nvar = self.local_num();
        let Some(continues) = self.continue_blocks.last_mut() else {
            panic!("continue outside loop");
        };
        self.fp.byte_codes.push(ByteCode::Jump(0));
        continues.push((self.fp.byte_codes.len() - 1, nvar));
        true
    }

    fn push_loop_block(&mut self) {
        self.breal_blocks.push(Vec::new());
        self.continue_blocks.push(Vec::new());
    }

    fn pop_loop_block(&mut self, icontinue: usize) {
        let iend = self.fp.byte_codes.len() - 1;
        for i in self.breal_blocks.pop().unwrap().into_iter() {
            self.fp.byte_codes[i] = ByteCode::Jump((iend - 1) as i16);
        }

        // continue
        let end_nvar = self.local_num();
        for (i, i_nvar) in self.continue_blocks.pop().unwrap().into_iter() {
            if i_nvar < end_nvar {
                panic!("continue jump into local scope");
            }
            self.fp.byte_codes[i] = ByteCode::Jump((icontinue as isize - i as isize) as i16 - 1);
        }
    }

    fn do_stat(&mut self) {
        assert_eq!(self.block(), Token::End);
    }

    fn label_stat(&mut self, igoto: usize) {
        let name = self.read_name();
        self.ctx.lex.expect(Token::DoubColon);

        // check if this label is at the end of block
        // ignore vpod syayments: `;` and label.
        let is_last = loop {
            match self.ctx.lex.peek() {
                Token::SemiColon => {
                    self.ctx.lex.next();
                }
                Token::DoubColon => {
                    self.ctx.lex.next();
                    self.label_stat(igoto)
                }
                t => break is_block_end(t)
            }
        };

        // check duplicate
        if self.labels.iter().any(|l| l.name == name) {
            panic!("duplicate label {name}")
        }

        let icode = self.fp.byte_codes.len();
        let nvar = self.loca_num();

        // match previous gotos
        let mut no_dsts = Vec::new();
        for goto in self.gotos.drain(igoto..) {
            if goto.name == name {
                if !is_last && goto.nvar < nvar {
                    panic!("goto jump into scope {}", goto.name);
                }
                let dist = icode - goto.icode;
                self.fp.byte_codes[goto.icode] = ByteCode::Jump(dist as i16 - 1)
            } else {
                no_dsts.push(goto)
            }
        }
        self.gotos.append(&mut no_dsts);

        // save the label for following gotos
        self.labels.push(GoToLabel {
            name,
            icode,
            nvar,
        })
    }

    fn goto_stat(&mut self) {
        let name = self.read_name();

        // match previous label
        if let Some(label) = self.labels.iter().rev().find(|l| l.name == name) {
            // find label
            let dist = self.fp.byte_codes.len() - label.icode;
            self.local_check_close(label.nvar);
            self.fp.byte_codes.push(ByteCode::Jump(-(dist as i16) - 1))
        } else {
            // not find label,push a fake byte code and save the goto
            self.fp.byte_codes.push(ByteCode::Jump(0));

            self.gotos.push(GoToLabel {
                name,
                icode: self.fp.byte_codes.len() - 1,
                nvar: self.local_num(),
            })
        }
    }

    fn ret_stat(&mut self) {
        let code = match self.ctx.lex.peek() {
            Token::SemiColon => {
                self.ctx.lex.next();
                ByteCode::Return0
            }
            t if is_block_end(t) => {
                ByteCode::Return0
            }
            _ => {
                let iret = self.sp;
                let (nexp, last_exp) = self.explist();

                // check optional ';'
                if self.ctx.lex.peek() == &Token::SemiColon {
                    self.ctx.lex.next();
                }

                // check block end
                if !is_block_end(self.ctx.lex.peek()) {
                    panic!("'end' expected");
                }

                if let (0, &ExpDesc::Local(i)) = (nexp, &last_exp) {
                    ByteCode::Return(i as u8, 1)
                } else if let (0, &ExpDesc::Call(func, narg_plus)) = (nexp, *last_exp) {
                    // tail call
                    ByteCode::TailCall(func as u8, narg_plus as u8)
                } else if self.discharge_try_expand(last_exp, 0) {
                    // return variable values
                    ByteCode::Return(iret as u8, 0)
                } else {
                    // return fixed values
                    ByteCode::Return(iret as u8, nexp as u8 + 1)
                }
            }
        };
        self.fp.byte_codes.push(code);
    }

    fn assign_var(&mut self,var:ExpDesc,value:ExpDesc){
        if let ExpDesc::Local(i) = var {
            self.discharge(i,value);
        }else {
            match self.discharge_const(value) {
                ConstStack::Const(i) => self.assign_from_const(var,i),
                ConstStack::Stack(i) => self.assign_from_stack(var,i),
            }
        }
    }

    fn assign_from_stack(&mut self,var:ExpDesc,value:usize){
        let code = match var {
            ExpDesc::Local(i) => ByteCode::Move(i as u8,value as u8),
            ExpDesc::UpValue(i) => ByteCode::SetUpValue(u as u8,value as u8),
            ExpDesc::Index(t, key) => ByteCode::SetTable(t as u8, key as u8, value as u8),
            ExpDesc::IndexField(t, key) => ByteCode::SetField(t as u8, key as u8, value as u8),
            ExpDesc::IndexInt(t, key) => ByteCode::SetInt(t as u8, key, value as u8),
            ExpDesc::IndexUpField(t, key) => ByteCode::SetUpField(t as u8, key as u8, value as u8),
            _ => panic!("assign from stack"),
        };
        self.fp.byte_codes.push(code);
    }

    fn assign_from_const(&mut self,var:ExpDesc,value:usize){
        let code = match var {
            ExpDesc::UpValue(i) => ByteCode::SetUpValueConst(i as u8,value as u8),
            ExpDesc::Index(t, key) => ByteCode::SetTableConst(t as u8, key as u8, value as u8),
            ExpDesc::IndexField(t, key) => ByteCode::SetFieldConst(t as u8, key as u8, value as u8),
            ExpDesc::IndexInt(t, key) => ByteCode::SetIntConst(t as u8, key, value as u8),
            ExpDesc::IndexUpField(t, key) => ByteCode::SetUpFieldConst(t as u8, key as u8, value as u8),
            _ => panic!("assign from const"),
        };
        self.fp.byte_codes.push(code);
    }

    // add the value to constants
    fn add_const(&mut self,c:impl Into<Value>) -> usize{
        let c = c.into();
        let constants = &mut self.fp.constants;
        constants.iter().position(|v|v.same(&c)).unwrap_or_else(||{
            constants.push(c);
            constants.len() - 1
        })
    }

    fn explist(&mut self) -> (usize,ExpDesc){
        let sp0 = self.sp;
        let mut n = 0;
        loop {
            let desc = self.exp();
            if self.ctx.lex.peek() != &Token::Comma{
                self.sp = sp0 + n;
                return (n,desc);
            }
            self.ctx.lex.next();

            self.discharge(sp0 + n,desc);
            n += 1;
        }
    }

    fn explist_want(&mut self,want:usize){
        let (nexp,last_exp) = self.explist();
        match (nexp + 1).cmp(&want) {
            Ordering::Equal => {
                self.discharge(self.sp,last_exp);
            }
            Ordering::Less => {
                // expand last expressions
                self.discharge_expand_want(last_exp,want - nexp);
            }
            Ordering::Greater => {
                self.sp -= nexp - want
            }
        }
    }


    fn local_new(&mut self, name: String) {
        self.ctx.levels.last_mut().unwrap().locals.push((name, false));
    }

    fn local_expire(&mut self, from: usize) {
        // drop locals
        let mut vars = self.ctx.levels.last_mut().unwrap().locals.drain(from..);

        // generate Close if any dropped local variable referred as upvalue
        if vars.any(|v| v.1) {
            self.fp.byte_codes.push(ByteCode::Close(from as u8))
        }
    }
}