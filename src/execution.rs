use super::alloc::{FuncAddr, FuncInst, ModInst, Store, Val};
use super::instruction::{BlockType, Instr, MemArg};
use super::module::Locals;
use failure::{format_err, Error};
use std::cell::RefCell;
use std::convert::{Into, TryFrom};
use std::io::Write;
use std::rc::Rc;
use std::slice;

pub(crate) enum Cont {
    Return,
    Continue,
}

#[derive(Debug)]
pub(crate) struct Frame {
    arity: usize,
    locals: Vec<Val>,
    module: Rc<RefCell<ModInst>>,
}

impl Frame {
    fn new() -> Self {
        Frame {
            arity: 0,
            locals: Vec::new(),
            module: Rc::new(RefCell::new(ModInst::new())),
        }
    }

    pub(crate) fn new_with(arity: usize, locals: Vec<Val>, modinst: Rc<RefCell<ModInst>>) -> Self {
        Frame {
            arity,
            locals,
            module: modinst,
        }
    }
}

#[derive(Debug)]
pub(crate) enum StackEntry {
    Val(Val),
    Label(Label),
    Frame(Rc<RefCell<Frame>>),
}

impl Into<StackEntry> for Val {
    fn into(self) -> StackEntry {
        StackEntry::Val(self)
    }
}

type Stack = Vec<StackEntry>;

#[derive(Debug)]
pub(crate) struct Label {
    arity: usize,
    instrs: Vec<Instr>,
}

impl Label {
    fn new() -> Self {
        Label {
            instrs: Vec::new(),
            arity: 0,
        }
    }

    fn new_with(arity: usize, instrs: Vec<Instr>) -> Self {
        Label { arity, instrs }
    }
}

fn eval(stack: &mut Stack, store: &mut Store, instr: &Instr) -> Result<Cont, Error> {
    use Instr::*;

    let frame = current_frame(stack)?;

    match instr {
        Const(val) => stack.push((*val).clone().into()),
        NumInstr(opcode) => eval_numinstr(stack, *opcode)?,
        Drop => match stack.pop() {
            Some(StackEntry::Val(_)) => {}
            _ => return Err(format_err!("Drop failed: stack head is not Val")),
        },
        Select => {
            let c = match stack.pop() {
                Some(StackEntry::Val(Val::I32(c))) => c,
                _ => return Err(format_err!("Select failed: stack head is not i32")),
            };

            let val1 = stack.pop();
            let val2 = stack.pop();
            match (val1, val2) {
                (Some(StackEntry::Val(v1)), Some(StackEntry::Val(v2))) => {
                    stack.push(if c == 0 { v1.into() } else { v2.into() });
                }
                _ => return Err(format_err!("Select failed: stack head is not Val")),
            }
        }
        LocalGet(x) => match frame.borrow().locals.get(*x as usize) {
            Some(v) => stack.push(v.clone().into()),
            _ => {
                return Err(format_err!(
                    "LocalGet failed: {} is out of bounds Frame.locales",
                    x
                ))
            }
        },
        LocalSet(x) => {
            if frame.borrow().locals.len() <= *x as usize {
                return Err(format_err!(
                    "LocalSet failed: {} is out of bounds Frame.locales",
                    x
                ));
            }

            match stack.pop() {
                Some(StackEntry::Val(v)) => {
                    frame.borrow_mut().locals[*x as usize] = v.into();
                }
                _ => return Err(format_err!("LocalSet failed: stack head is not Val")),
            };
        }
        LocalTee(x) => {
            match stack.pop() {
                Some(StackEntry::Val(v)) => {
                    stack.push(v.clone().into());
                    stack.push(v.into());
                }
                _ => return Err(format_err!("LocalTee failed: stack head is not Val")),
            }

            eval(stack, store, &LocalSet(*x))?;
        }
        GlobalGet(x) => {
            let a = *frame
                .borrow()
                .module
                .borrow()
                .globals
                .get(*x as usize)
                .ok_or(format_err!(
                    "GlobalGet failed: module.globals index out of bounds({})",
                    x
                ))?;

            let glob = store.globals.get(a as usize).ok_or(format_err!(
                "GlobalGet failed: module.globals index out of bounds({})",
                x
            ))?;

            stack.push(glob.val.clone().into());
        }
        GlobalSet(x) => {
            let a = *frame
                .borrow()
                .module
                .borrow()
                .globals
                .get(*x as usize)
                .ok_or(format_err!(
                    "GlobalSet failed: module.globals index out of bounds({})",
                    x
                ))?;

            let mut glob = store.globals.get_mut(a as usize).ok_or(format_err!(
                "GlobalGet failed: module.globals index out of bounds({})",
                x
            ))?;

            // Checking for Mutability is nothing?

            match stack.pop() {
                Some(StackEntry::Val(v)) => glob.val = v.clone(),
                _ => return Err(format_err!("GlobalSet failed: stack head is not Val")),
            };
        }
        MemInstr(opcode, memarg) => eval_meminstr(stack, store, *opcode, memarg)?,
        MemSize => eval_memsize(stack, store)?,
        MemGrow => eval_memgrow(stack, store)?,

        // Control Instructions
        Nop => {}
        Unreachable => return Err(format_err!("Unrachable!")),
        Block(blocktype, instrs) => {
            let arity = match blocktype {
                BlockType::Unit => 0,
                _ => 1,
            };

            let l = Label::new_with(arity, Vec::new());
            stack.push(StackEntry::Label(l));

            return eval_instrs(stack, store, instrs);
        }
        Loop(_blocktype, instrs) => {
            let l = Label::new_with(0, instrs.clone()); // FIXME: clone
            stack.push(StackEntry::Label(l));
            match eval_instrs(stack, store, instrs)? {
                Cont::Return => return Ok(Cont::Return),
                _ => {
                    return eval(stack, store, instr);
                }
            }
        }
        If(blocktype, then, els) => {
            let c = match stack.pop() {
                Some(StackEntry::Val(Val::I32(c))) => c,
                _ => return Err(format_err!("If failed: stack head is not a Val::I32")),
            };

            if c != 0 {
                return eval(stack, store, &Block((*blocktype).clone(), then.clone()));
            } else {
                return eval(stack, store, &Block((*blocktype).clone(), els.clone()));
            }
        }
        Br(lidx) => {
            // Assert: due to validation, the stack contains at least lidx+1 labels.
            let lidx = *lidx as usize;

            let n = {
                let l = stack
                    .iter()
                    .rev()
                    .filter_map(|v| {
                        if let StackEntry::Label(label) = v {
                            Some(label)
                        } else {
                            None
                        }
                    })
                    .nth(lidx + 1)
                    .ok_or(format_err!(
                        "Br failed: labels in stack less than {}",
                        lidx + 1
                    ))?;

                l.arity
            };

            let mut valn = Vec::new();
            for _ in 0..n {
                match stack.pop() {
                    Some(v @ StackEntry::Val(_)) => valn.push(v),
                    _ => {
                        return Err(format_err!(
                            "Br failed: stack head have something without Val"
                        ))
                    }
                }
            }

            let mut l = Label::new();
            for _ in 0..(lidx + 1) {
                match stack.pop() {
                    Some(StackEntry::Val(_)) => {}
                    Some(StackEntry::Label(label)) => l = label,
                    _ => {
                        return Err(format_err!(
                            "Br failed: stack head have something without Val"
                        ))
                    }
                }
            }

            while let Some(v) = valn.pop() {
                stack.push(v);
            }

            return eval_instrs(stack, store, &l.instrs);
        }
        BrIf(lidx) => {
            let c = match stack.pop() {
                Some(StackEntry::Val(Val::I32(c))) => c,
                _ => return Err(format_err!("BrIf failed: stack head is not a Val::I32")),
            };

            if c == 0 {
                return eval(stack, store, &Br(*lidx));
            }
        }
        BrTable(ls, lidx) => {
            let i = match stack.pop() {
                Some(StackEntry::Val(Val::I32(i))) => i,
                _ => return Err(format_err!("BrTable failed: stack head is not a Val::I32")),
            } as usize;

            if i < ls.len() {
                return eval(stack, store, &Br(ls[i]));
            } else {
                return eval(stack, store, &Br(*lidx));
            }
        }
        Return => {
            return_proc(stack)?;

            return Ok(Cont::Return);
        }
        Call(x) => {
            let x = *x as usize;

            let a = *frame
                .borrow()
                .module
                .borrow()
                .funcs
                .get(x)
                .ok_or(format_err!(
                    "Call failed: x is out of bounds F.module.funcaddrs({})",
                    x
                ))?;

            match invoke(a, stack, store)? {
                Cont::Continue => return_proc(stack)?,
                _ => {}
            };
        }
        CallIndirect(x) => {
            let x = *x as usize;

            let ta = *frame
                .borrow()
                .module
                .borrow()
                .tables
                .get(0)
                .ok_or(format_err!(
                    "CallIndirect failed: F.module.tableaddrs[0] is not exist"
                ))? as usize;

            let tab = store
                .tables
                .get(ta)
                .ok_or(format_err!("CallIndirect failed: S.table[ta] is not exist"))?;

            let ft_expect = frame
                .borrow()
                .module
                .borrow()
                .types
                .get(x)
                .ok_or(format_err!(
                    "CallIndirect failed: F.module.types[x] is not exist"
                ))?
                .clone();

            let i = match stack.pop() {
                Some(StackEntry::Val(Val::I32(i))) => i,
                _ => {
                    return Err(format_err!(
                        "CallIndirect failed: stack head is not a i32.const"
                    ))
                }
            } as usize;

            if tab.elems.len() <= i {
                // FIXME: Trap
                return Err(format_err!("CallIndirect Trap"));
            }

            let a = match tab.elems[i] {
                None => {
                    // FIXME: Trap
                    return Err(format_err!("CallIndirect Trap"));
                }
                Some(addr) => addr,
            };

            let f = store
                .funcs
                .get(a)
                .ok_or(format_err!("CallIndirect failed: S.funcs[a] is not exist"))?;

            match f {
                FuncInst::WasmFuncInst(f) => {
                    if f.functype != ft_expect {
                        // FIXME: Trap
                        return Err(format_err!("CallIndirect Trap"));
                    }
                }
                _ => {}
            }

            match invoke(a, stack, store)? {
                Cont::Continue => return_proc(stack)?,
                _ => {}
            };
        }
    }

    Ok(Cont::Continue)
}

fn current_frame(stack: &mut Stack) -> Result<Rc<RefCell<Frame>>, Error> {
    stack
        .iter()
        .rev()
        .find_map(|e| match e {
            StackEntry::Frame(f) => Some(f.clone()),
            _ => None,
        })
        .ok_or(format_err!("Stack have no frame"))
}

fn eval_instrs(stack: &mut Stack, store: &mut Store, instrs: &[Instr]) -> Result<Cont, Error> {
    for instr in instrs.iter() {
        if let Cont::Return = eval(stack, store, instr)? {
            return Ok(Cont::Return);
        }
    }
    Ok(Cont::Continue)
}

fn unop<A, R, F>(stack: &mut Stack, f: F) -> Result<(), Error>
where
    F: Fn(A) -> R,
    A: TryFrom<Val>,
    <A as TryFrom<Val>>::Error: Into<Error>,
    R: Into<Val>,
{
    match stack.pop() {
        Some(StackEntry::Val(v)) => {
            let v = A::try_from(v).map_err(|e| e.into())?;
            stack.push(StackEntry::Val(f(v).into()));
            Ok(())
        }
        item => Err(format_err!("unop stack head isn't Val: {:?}", item)),
    }
}

fn binop<A1, A2, R, F>(stack: &mut Stack, f: F) -> Result<(), Error>
where
    F: Fn(A1, A2) -> R,
    A1: TryFrom<Val>,
    <A1 as TryFrom<Val>>::Error: Into<Error>,
    A2: TryFrom<Val>,
    <A2 as TryFrom<Val>>::Error: Into<Error>,
    R: Into<Val>,
{
    let c2 = stack.pop();
    let c1 = stack.pop();

    match (c1, c2) {
        (Some(StackEntry::Val(c1)), Some(StackEntry::Val(c2))) => {
            let c1 = A1::try_from(c1).map_err(|e| e.into())?;
            let c2 = A2::try_from(c2).map_err(|e| e.into())?;
            stack.push(StackEntry::Val(f(c1, c2).into()));
            Ok(())
        }
        item => Err(format_err!("binop stack head isn't Val: {:?}", item)),
    }
}

fn eval_numinstr(stack: &mut Stack, opcode: u8) -> Result<(), Error> {
    match opcode {
        0x45 => unop(stack, |c: u32| eq(c, 0)),
        0x46 => binop(stack, eq::<u32>),
        0x47 => binop(stack, |i1, i2| !eq::<u32>(i1, i2)),
        0x48 => binop(stack, |i1: u32, i2: u32| lt(i1 as i32, i2 as i32)),
        0x49 => binop(stack, lt::<u32>),
        0x4A => binop(stack, |i1: u32, i2: u32| gt(i1 as i32, i2 as i32)),
        0x4B => binop(stack, gt::<u32>),
        0x4C => binop(stack, |i1: u32, i2: u32| le(i1 as i32, i2 as i32)),
        0x4D => binop(stack, le::<u32>),
        0x4E => binop(stack, |i1: u32, i2: u32| ge(i1 as i32, i2 as i32)),
        0x4F => binop(stack, ge::<u32>),

        0x50 => unop(stack, |c: u64| eq(c, 0)),
        0x51 => binop(stack, eq::<u64>),
        0x52 => binop(stack, |i1, i2| !eq::<u64>(i1, i2)),
        0x53 => binop(stack, |i1: u64, i2: u64| lt(i1 as i64, i2 as i64)),
        0x54 => binop(stack, lt::<u64>),
        0x55 => binop(stack, |i1: u64, i2: u64| gt(i1 as i64, i2 as i64)),
        0x56 => binop(stack, gt::<u64>),
        0x57 => binop(stack, |i1: u64, i2: u64| le(i1 as i64, i2 as i64)),
        0x58 => binop(stack, le::<u64>),
        0x59 => binop(stack, |i1: u64, i2: u64| ge(i1 as i64, i2 as i64)),
        0x5A => binop(stack, ge::<u64>),

        0x5B => binop(stack, eq::<f32>),
        0x5C => binop(stack, |i1, i2| !eq::<f32>(i1, i2)),
        0x5D => binop(stack, lt::<f32>),
        0x5E => binop(stack, gt::<f32>),
        0x5F => binop(stack, le::<f32>),
        0x60 => binop(stack, ge::<f32>),

        0x61 => binop(stack, eq::<f64>),
        0x62 => binop(stack, |i1, i2| !eq::<f64>(i1, i2)),
        0x63 => binop(stack, lt::<f64>),
        0x64 => binop(stack, gt::<f64>),
        0x65 => binop(stack, le::<f64>),
        0x66 => binop(stack, ge::<f64>),

        0x67 => unimplemented!(), // i32.clz
        0x68 => unimplemented!(), // i32.ctz
        0x69 => unimplemented!(), // i32.popcnt

        0x6A => binop(stack, add_i32),
        0x6B => binop(stack, sub_i32),
        0x6C => binop(stack, mul_i32),
        0x6D => binop(stack, |i1: u32, i2: u32| (i1 as i32 / i2 as i32) as u32),
        0x6E => binop(stack, |i1: u32, i2: u32| i1 / i2),
        0x6F => binop(stack, |i1: u32, i2: u32| (i1 as i32 % i2 as i32) as u32),
        0x70 => binop(stack, |i1: u32, i2: u32| i1 % i2),
        0x71 => binop(stack, |i1: u32, i2: u32| i1 & i2),
        0x72 => binop(stack, |i1: u32, i2: u32| i1 | i2),
        0x73 => binop(stack, |i1: u32, i2: u32| i1 ^ i2),
        0x74 => binop(stack, shl_i32),
        0x75 => binop(stack, shr_s_i32),
        0x76 => binop(stack, shr_u_i32),
        0x77 => binop(stack, rotl_i32),
        0x78 => binop(stack, rotr_i32),

        0x79 => unimplemented!(), // i32.clz
        0x7A => unimplemented!(), // i32.ctz
        0x7B => unimplemented!(), // i32.popcnt

        0x7C => binop(stack, add_i64),
        0x7D => binop(stack, sub_i64),
        0x7E => binop(stack, mul_i64),
        0x7F => binop(stack, |i1: u64, i2: u64| (i1 as i64 / i2 as i64) as u64),
        0x80 => binop(stack, |i1: u64, i2: u64| i1 / i2),
        0x81 => binop(stack, |i1: u64, i2: u64| (i1 as i64 % i2 as i64) as u64),
        0x82 => binop(stack, |i1: u64, i2: u64| i1 % i2),
        0x83 => binop(stack, |i1: u64, i2: u64| i1 & i2),
        0x84 => binop(stack, |i1: u64, i2: u64| i1 | i2),
        0x85 => binop(stack, |i1: u64, i2: u64| i1 ^ i2),
        0x86 => binop(stack, shl_i64),
        0x87 => binop(stack, shr_s_i64),
        0x88 => binop(stack, shr_u_i64),
        0x89 => binop(stack, rotl_i64),
        0x8A => binop(stack, rotr_i64),

        0x8B => unop(stack, |z: f32| z.abs()),
        0x8C => unop(stack, |z: f32| -z),
        0x8D => unop(stack, |z: f32| z.ceil()),
        0x8E => unop(stack, |z: f32| z.floor()),
        0x8F => unop(stack, |z: f32| z.trunc()),
        0x90 => unop(stack, |z: f32| nearest_f32(z)),
        0x91 => unop(stack, |z: f32| z.sqrt()),
        0x92 => binop(stack, |z1: f32, z2: f32| z1 + z2),
        0x93 => binop(stack, |z1: f32, z2: f32| z1 - z2),
        0x94 => binop(stack, |z1: f32, z2: f32| z1 * z2),
        0x95 => binop(stack, |z1: f32, z2: f32| z1 / z2),
        0x96 => binop(stack, |z1: f32, z2: f32| min_f32(z1, z2)),
        0x97 => binop(stack, |z1: f32, z2: f32| max_f32(z1, z2)),
        0x98 => binop(stack, |z1: f32, z2: f32| z1 * (z2 / z2.abs())),

        0x99 => unop(stack, |z: f64| z.abs()),
        0x9A => unop(stack, |z: f64| -z),
        0x9B => unop(stack, |z: f64| z.ceil()),
        0x9C => unop(stack, |z: f64| z.floor()),
        0x9D => unop(stack, |z: f64| z.trunc()),
        0x9E => unop(stack, |z: f64| nearest_f64(z)),
        0x9F => unop(stack, |z: f64| z.sqrt()),
        0xA0 => binop(stack, |z1: f64, z2: f64| z1 + z2),
        0xA1 => binop(stack, |z1: f64, z2: f64| z1 - z2),
        0xA2 => binop(stack, |z1: f64, z2: f64| z1 * z2),
        0xA3 => binop(stack, |z1: f64, z2: f64| z1 / z2),
        0xA4 => binop(stack, |z1: f64, z2: f64| min_f64(z1, z2)),
        0xA5 => binop(stack, |z1: f64, z2: f64| max_f64(z1, z2)),
        0xA6 => binop(stack, |z1: f64, z2: f64| z1 * (z2 / z2.abs())),

        0xA7 => unop(stack, |i: u64| (i % 2u64.pow(32)) as u32), // wrap
        0xA8 => unop(stack, |z: f32| z.trunc() as u32),          // trunc_s
        0xA9 => unop(stack, |z: f32| z.trunc() as u32),          // trunc_u
        0xAA => unop(stack, |z: f64| z.trunc() as u32),          // trunc_s
        0xAB => unop(stack, |z: f64| z.trunc() as u32),          // trunc_u
        0xAC => unop(stack, |i: u32| i as i32 as i64 as u64),    // extend_s
        0xAD => unop(stack, |i: u32| i as u64),                  // extend_u
        0xAE => unop(stack, |z: f32| z.trunc() as u64),          // trunc_s
        0xAF => unop(stack, |z: f32| z.trunc() as u64),          // trunc_u
        0xB0 => unop(stack, |z: f64| z.trunc() as u64),          // trunc_s
        0xB1 => unop(stack, |z: f64| z.trunc() as u64),          // trunc_u
        0xB2 => unop(stack, |i: u32| i as i32 as f32),           // convert_s
        0xB3 => unop(stack, |i: u32| i as f32),                  // convert_u
        0xB4 => unop(stack, |i: u64| i as i64 as f32),           // convert_s
        0xB5 => unop(stack, |i: u64| i as f32),                  // convert_u
        0xB6 => unop(stack, |z: f64| z as f32),                  // demote
        0xB7 => unop(stack, |i: u32| i as i32 as f64),           // convert_s
        0xB8 => unop(stack, |i: u32| i as f64),                  // convert_u
        0xB9 => unop(stack, |i: u64| i as i64 as f64),           // convert_s
        0xBA => unop(stack, |i: u64| i as f64),                  // convert_u
        0xBB => unop(stack, |z: f32| z as f64),                  // demote
        0xBC => unop(stack, |z: f32| unsafe {
            std::mem::transmute::<f32, u32>(z)
        }),
        0xBD => unop(stack, |z: f64| unsafe {
            std::mem::transmute::<f64, u64>(z)
        }),
        0xBE => unop(stack, |i: u32| unsafe {
            std::mem::transmute::<u32, f32>(i)
        }),

        0xBF => unop(stack, |i: u64| unsafe {
            std::mem::transmute::<u64, f64>(i)
        }),

        _ => Err(format_err!("invalid opcode: 0x{:x}", opcode)),
    }
}

fn eq<T: PartialEq>(i1: T, i2: T) -> u32 {
    i1.eq(&i2) as u32
}

fn lt<T: PartialOrd>(i1: T, i2: T) -> u32 {
    i1.lt(&i2) as u32
}

fn gt<T: PartialOrd>(i1: T, i2: T) -> u32 {
    i1.gt(&i2) as u32
}

fn le<T: PartialOrd>(i1: T, i2: T) -> u32 {
    i1.le(&i2) as u32
}

fn ge<T: PartialOrd>(i1: T, i2: T) -> u32 {
    i1.ge(&i2) as u32
}

fn add_i32(i1: u32, i2: u32) -> u32 {
    ((i1 as u64 + i2 as u64) % 2_u64.pow(32)) as u32
}

fn sub_i32(i1: u32, i2: u32) -> u32 {
    let x = 2_u64.pow(32);
    ((i1 as u64 - i2 as u64 + x) % x) as u32
}

fn mul_i32(i1: u32, i2: u32) -> u32 {
    ((i1 as u64 * i2 as u64) % 2_u64.pow(32)) as u32
}

fn shl_i32(i1: u32, i2: u32) -> u32 {
    let k = i2 % 32;
    i1 << k
}

fn shr_s_i32(i1: u32, i2: u32) -> u32 {
    let k = i2 % 32;
    let d0 = i1 & (1 << 31);
    let mut r = i1;
    for _ in 0..k {
        r >>= 1;
        r |= d0;
    }

    r
}

fn shr_u_i32(i1: u32, i2: u32) -> u32 {
    let k = i2 % 32;
    i1 >> k
}

fn rotl_i32(i1: u32, i2: u32) -> u32 {
    let k = i2 % 32;
    (i1 << k) | (i1 >> (i1 >> (32 - k)))
}

fn rotr_i32(i1: u32, i2: u32) -> u32 {
    let k = i2 % 32;
    (i1 >> k) | (i1 << (i1 >> (32 - k)))
}

// for u64

fn add_i64(i1: u64, i2: u64) -> u64 {
    ((i1 as u128 + i2 as u128) % 2_u128.pow(64)) as u64
}

fn sub_i64(i1: u64, i2: u64) -> u64 {
    let x = 2_i128.pow(64);
    ((i1 as i128 - i2 as i128 + x) % x) as u64
}

fn mul_i64(i1: u64, i2: u64) -> u64 {
    ((i1 as u128 * i2 as u128) % 2_u128.pow(64)) as u64
}

fn shl_i64(i1: u64, i2: u64) -> u64 {
    let k = i2 % 64;
    i1 << k
}

fn shr_s_i64(i1: u64, i2: u64) -> u64 {
    let k = i2 % 64;
    let d0 = i1 & (1 << 31);
    let mut r = i1;
    for _ in 0..k {
        r >>= 1;
        r |= d0;
    }

    r
}

fn shr_u_i64(i1: u64, i2: u64) -> u64 {
    let k = i2 % 64;
    i1 >> k
}

fn rotl_i64(i1: u64, i2: u64) -> u64 {
    let k = i2 % 64;
    (i1 << k) | (i1 >> (i1 >> (64 - k)))
}

fn rotr_i64(i1: u64, i2: u64) -> u64 {
    let k = i2 % 64;
    (i1 >> k) | (i1 << (i1 >> (64 - k)))
}

fn nearest_f32(z: f32) -> f32 {
    if (z - z.ceil()).abs() < 0.5 {
        z.ceil()
    } else if (z - z.floor()).abs() < 0.5 {
        z.floor()
    } else {
        nearest_f32(z / 2f32) * 2f32
    }
}

fn min_f32(z1: f32, z2: f32) -> f32 {
    if z1.is_nan() || z2.is_nan() {
        std::f32::NAN
    } else {
        if z1 <= z2 {
            z1
        } else {
            z2
        }
    }
}

fn max_f32(z1: f32, z2: f32) -> f32 {
    if z1.is_nan() || z2.is_nan() {
        std::f32::NAN
    } else {
        if z1 >= z2 {
            z1
        } else {
            z2
        }
    }
}

fn nearest_f64(z: f64) -> f64 {
    if (z - z.ceil()).abs() < 0.5 {
        z.ceil()
    } else if (z - z.floor()).abs() < 0.5 {
        z.floor()
    } else {
        nearest_f64(z / 2f64) * 2f64
    }
}

fn min_f64(z1: f64, z2: f64) -> f64 {
    if z1.is_nan() || z2.is_nan() {
        std::f64::NAN
    } else {
        if z1 <= z2 {
            z1
        } else {
            z2
        }
    }
}

fn max_f64(z1: f64, z2: f64) -> f64 {
    if z1.is_nan() || z2.is_nan() {
        std::f64::NAN
    } else {
        if z1 >= z2 {
            z1
        } else {
            z2
        }
    }
}

fn eval_meminstr(
    stack: &mut Stack,
    store: &mut Store,
    opcode: u8,
    memarg: &MemArg,
) -> Result<(), Error> {
    match opcode {
        0x28 => load_mem::<u32, u32>(stack, store, memarg)?,
        0x29 => load_mem::<u64, u64>(stack, store, memarg)?,
        0x2A => load_mem::<f32, f32>(stack, store, memarg)?,
        0x2B => load_mem::<f64, f64>(stack, store, memarg)?,
        0x2C => load_mem::<i32, i8>(stack, store, memarg)?,
        0x2D => load_mem::<u32, u8>(stack, store, memarg)?,
        0x2E => load_mem::<i32, i16>(stack, store, memarg)?,
        0x2F => load_mem::<u32, u16>(stack, store, memarg)?,
        0x30 => load_mem::<i64, i8>(stack, store, memarg)?,
        0x31 => load_mem::<u64, u8>(stack, store, memarg)?,
        0x32 => load_mem::<i64, i16>(stack, store, memarg)?,
        0x33 => load_mem::<u64, u16>(stack, store, memarg)?,
        0x34 => load_mem::<i64, i32>(stack, store, memarg)?,
        0x35 => load_mem::<u64, u32>(stack, store, memarg)?,

        0x36 => store_mem::<u32, u32>(stack, store, memarg)?,
        0x37 => store_mem::<u64, u64>(stack, store, memarg)?,
        0x38 => store_mem::<f32, f32>(stack, store, memarg)?,
        0x39 => store_mem::<f64, f64>(stack, store, memarg)?,
        0x3A => store_mem::<u32, u8>(stack, store, memarg)?,
        0x3B => store_mem::<u32, u16>(stack, store, memarg)?,
        0x3C => store_mem::<u64, u8>(stack, store, memarg)?,
        0x3D => store_mem::<u64, u16>(stack, store, memarg)?,
        0x3E => store_mem::<u64, u32>(stack, store, memarg)?,

        _ => return Err(format_err!("Invalid Mem Instr: 0x{:x}", opcode)),
    }
    Ok(())
}

fn load_mem<T, F>(stack: &mut Stack, store: &mut Store, memarg: &MemArg) -> Result<(), Error>
where
    T: Into<Val>,
    F: Into<T>,
{
    let frame = current_frame(stack)?;
    let n = std::mem::size_of::<F>();

    let a = *frame
        .borrow()
        .module
        .borrow()
        .mems
        .get(0)
        .ok_or(format_err!("load_mem failed: memaddrs[0] not found"))?;

    let mem = store
        .mems
        .get(a as usize)
        .ok_or(format_err!("load_mem failed: S.mems[a] not found"))?;

    let i = match stack.pop() {
        Some(StackEntry::Val(Val::I32(v))) => v,
        _ => return Err(format_err!("load_mem failed: stack head is not i32.const")),
    };

    let ea = (i + memarg.offset) as usize;

    if mem.data.len() < (ea + n / 8) {
        return Err(format_err!(
            "load_mem failed: mem.data too smaller then {}",
            ea + n / 8
        ));
    }

    let c: T = unsafe {
        let b = std::ptr::read(mem.data[ea..(ea + n / 8)].as_ptr() as *const F);
        b.into()
    };

    stack.push(c.into().into());

    Ok(())
}

fn store_mem<T, F>(stack: &mut Stack, store: &mut Store, memarg: &MemArg) -> Result<(), Error>
where
    T: TryFrom<Val>,
    <T as TryFrom<Val>>::Error: Into<Error>,
    F: Into<T>, // size_of::<F>() < size_of::<T>() ?
{
    let frame = current_frame(stack)?;
    let n = std::mem::size_of::<F>();

    let a = *frame
        .borrow()
        .module
        .borrow()
        .mems
        .get(0)
        .ok_or(format_err!("store_mem failed: memaddrs[0] not found"))?;

    let mem = store
        .mems
        .get_mut(a as usize)
        .ok_or(format_err!("store_mem failed: S.mems[a] not found"))?;

    let c = match stack.pop() {
        Some(StackEntry::Val(v)) => v,
        _ => return Err(format_err!("store_mem failed: stack head is not i32.const")),
    };
    let c = T::try_from(c).map_err(|e| e.into())?;

    let i = match stack.pop() {
        Some(StackEntry::Val(Val::I32(v))) => v,
        _ => return Err(format_err!("store_mem failed: stack head is not i32.const")),
    };

    let ea = (i + memarg.offset) as usize;

    if mem.data.len() < (ea + n / 8) {
        return Err(format_err!(
            "load_mem failed: mem.data too smaller then {}",
            ea + n / 8
        ));
    }

    let bs = unsafe { slice::from_raw_parts(&c as *const T as *const u8, n / 8) };

    mem.data[ea..(ea + n / 8)].as_mut().write_all(&bs)?;

    Ok(())
}

fn eval_memsize(stack: &mut Stack, store: &mut Store) -> Result<(), Error> {
    let frame = current_frame(stack)?;

    let a = *frame
        .borrow()
        .module
        .borrow()
        .mems
        .get(0)
        .ok_or(format_err!("store_mem failed: memaddrs[0] not found"))?;

    let mem = store
        .mems
        .get(a as usize)
        .ok_or(format_err!("store_mem failed: S.mems[a] not found"))?;

    let sz = (mem.data.len() / 64 / 1024) as u32;

    stack.push(StackEntry::Val(sz.into()));

    Ok(())
}

fn eval_memgrow(stack: &mut Stack, store: &mut Store) -> Result<(), Error> {
    let frame = current_frame(stack)?;

    let a = *frame
        .borrow()
        .module
        .borrow()
        .mems
        .get(0)
        .ok_or(format_err!("store_mem failed: memaddrs[0] not found"))?;

    let mem = store
        .mems
        .get_mut(a as usize)
        .ok_or(format_err!("store_mem failed: S.mems[a] not found"))?;

    let sz = (mem.data.len() / 64 / 1024) as u32;

    let n = match stack.pop() {
        Some(StackEntry::Val(Val::I32(v))) => v,
        _ => return Err(format_err!("memgrow failed: stack head is not i32.const")),
    };

    let len = sz + n;

    if len > 2u32.pow(16) || mem.max < len {
        stack.push(StackEntry::Val(Val::I32(-1i32 as u32))); // Fail
        return Ok(());
    }

    mem.data.extend(vec![0; n as usize * 64 * 1024]);

    Ok(())
}

pub(crate) fn invoke(a: FuncAddr, stack: &mut Stack, store: &mut Store) -> Result<Cont, Error> {
    use FuncInst::*;

    let f = store
        .funcs
        .get(a)
        .ok_or(format_err!("invoke failed: store have a FuncAddr a({})", a))?;

    // TODO: Assert: due to validataion, m <= 1

    match f {
        WasmFuncInst(f) => {
            let n = f.functype.0.len();
            let m = f.functype.1.len();

            // TODO: Assert: due to vlidation, m<=1

            let mut valn = Vec::new();
            for _ in 0..n {
                match stack.pop() {
                    Some(StackEntry::Val(v)) => valn.push(v),
                    _ => {
                        return Err(format_err!(
                            "invoke failed: stack head have something without Val"
                        ))
                    }
                }
            }

            valn.append(
                &mut f
                    .code
                    .locals
                    .iter()
                    .map(|Locals(_, t)| t.zero_val())
                    .collect::<Vec<_>>(),
            );

            let frame = Rc::new(RefCell::new(Frame::new_with(m, valn, f.modinst.clone())));
            stack.push(StackEntry::Frame(frame));

            let blocktype = if f.functype.1.len() == 0 {
                BlockType::Unit
            } else {
                BlockType::ValType(f.functype.1[0].clone())
            };
            let instr = Instr::Block(blocktype, f.code.expr.clone());

            return eval(stack, store, &instr);
        }
        _ => {
            // TODO: Host Function
        }
    }
    Ok(Cont::Continue)
}

fn return_proc(stack: &mut Stack) -> Result<(), Error> {
    let frame = current_frame(stack)?;

    let n = frame.borrow().arity;
    let mut valn = Vec::new();
    for _ in 0..n {
        match stack.pop() {
            Some(v @ StackEntry::Val(_)) => valn.push(v),
            _ => {
                return Err(format_err!(
                    "Return failed: stack head have something without Val"
                ))
            }
        }
    }

    loop {
        match stack.pop() {
            Some(StackEntry::Frame(_)) => break,
            None => return Err(format_err!("Return failed: stack have no frame")),
            _ => {}
        }
    }

    while let Some(v) = valn.pop() {
        stack.push(v);
    }

    Ok(())
}

pub(crate) fn eval_expr(
    stack: &mut Stack,
    store: &mut Store,
    instrs: &[Instr],
) -> Result<Val, Error> {
    for instr in instrs.iter() {
        if let Cont::Return = eval(stack, store, instr)? {
            break;
        }
    }

    match stack.pop() {
        Some(StackEntry::Val(v)) => Ok(v),
        _ => Err(format_err!("eval_expr failed: stack head is not Val")),
    }
}

#[test]
fn eval_test() {
    use super::alloc::Val::*;
    use super::instruction::Instr::*;
    //    use StackEntry::*;

    {
        let mut s = Stack::new();
        let mut store = Store::new();
        let mut frame = Frame::new();
        s.push(StackEntry::Val(I32(0)));
        eval(&mut s, &mut store, &mut frame, &NumInstr(0x45));
        assert_eq!(s.pop(), Some(StackEntry::Val(I32(1))));
    }

    {
        let mut s = Stack::new();
        let mut store = Store::new();
        let mut frame = Frame::new();
        s.push(StackEntry::Val(I64(3)));
        s.push(StackEntry::Val(I64(3)));
        eval(&mut s, &mut store, &mut frame, &NumInstr(0x51));
        assert_eq!(s.pop(), Some(StackEntry::Val(I32(1))));
    }
}
