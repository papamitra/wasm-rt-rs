use super::alloc::Val;
use super::leb128::ReadLEB128Ext;
use super::module::{valtype, vec, ValType};
use byteorder::{LittleEndian, ReadBytesExt};
use failure::format_err;
use failure::Error;
use std::io::{BufRead, BufReader, Read};

#[derive(Clone, PartialEq, Debug)]
pub(crate) enum Instr {
    Unreachable,
    Nop,
    Block(BlockType, Vec<Instr>),
    Loop(BlockType, Vec<Instr>),
    If(BlockType, Vec<Instr>, Vec<Instr>),
    Br(u32),
    BrIf(u32),
    BrTable(Vec<u32>, u32),
    Return,
    Call(u32),
    CallIndirect(u32),
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    MemInstr(u8, MemArg),
    MemSize,
    MemGrow,
    Const(Val),
    NumInstr(u8),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum BlockType {
    Unit,
    ValType(ValType),
}

fn blocktype<R>(r: &mut R) -> Result<BlockType, Error>
where
    R: Read,
{
    use BlockType::*;

    match r.read_u8()? {
        0x40 => Ok(Unit),
        other => Ok(ValType(valtype(other)?)),
    }
}

fn expect<R>(r: &mut R, ex: u8) -> Result<(), Error>
where
    R: Read,
{
    let b = r.read_u8()?;
    if b != ex {
        return Err(format_err!(
            "Unexpected byte 0x{:x}, expected 0x{:x}",
            b,
            ex
        ));
    }

    Ok(())
}

fn prefetch<R>(r: &mut R) -> Result<u8, Error>
where
    R: BufRead,
{
    let buf = r.fill_buf()?;
    if buf.len() == 0 {
        return Err(format_err!("Unexpected Eof"));
    }

    Ok(buf[0])
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct MemArg {
    align: u32,
    pub(crate) offset: u32,
}

fn memarg<R: Read>(r: &mut BufReader<R>) -> Result<MemArg, Error> {
    Ok(MemArg {
        align: r.read_u32_leb128()?,
        offset: r.read_u32_leb128()?,
    })
}

pub(crate) fn instr<R: Read>(bs: &mut BufReader<R>) -> Result<Instr, Error> {
    use Instr::*;

    match bs.read_u8()? {
        0x00 => Ok(Unreachable),
        0x01 => Ok(Nop),
        0x02 => {
            let rt = blocktype(bs)?;
            let mut ins = Vec::new();
            while prefetch(bs)? != 0x0B {
                ins.push(instr(bs)?);
            }
            bs.consume(1);
            Ok(Block(rt, ins))
        }
        0x03 => {
            let rt = blocktype(bs)?;
            let mut ins = Vec::new();
            while prefetch(bs)? != 0x0B {
                ins.push(instr(bs)?);
            }
            bs.consume(1);
            Ok(Loop(rt, ins))
        }
        0x04 => {
            let rt = blocktype(bs)?;
            let mut ins1 = Vec::new();
            loop {
                match prefetch(bs)? {
                    0x0B => {
                        bs.consume(1);
                        return Ok(If(rt, ins1, Vec::new()));
                    }
                    0x05 => {
                        bs.consume(1);
                        break;
                    }
                    _ => {}
                };

                ins1.push(instr(bs)?);
            }

            let mut ins2 = Vec::new();
            while prefetch(bs)? != 0x0B {
                ins2.push(instr(bs)?);
            }

            bs.consume(1);
            Ok(If(rt, ins1, ins2))
        }
        0x0C => Ok(Br(bs.read_u32_leb128()?)),
        0x0D => Ok(BrIf(bs.read_u32_leb128()?)),
        0x0E => Ok(BrTable(
            vec(bs, |r| r.read_u32_leb128())?,
            bs.read_u32_leb128()?,
        )),
        0x0F => Ok(Return),
        0x10 => Ok(Call(bs.read_u32_leb128()?)),
        0x11 => {
            let ret = CallIndirect(bs.read_u32_leb128()?);
            expect(bs, 0x00)?;
            Ok(ret)
        }
        0x1A => Ok(Drop),
        0x1B => Ok(Select),
        0x20 => Ok(LocalGet(bs.read_u32_leb128()?)),
        0x21 => Ok(LocalSet(bs.read_u32_leb128()?)),
        0x22 => Ok(LocalTee(bs.read_u32_leb128()?)),
        0x23 => Ok(GlobalGet(bs.read_u32_leb128()?)),
        0x24 => Ok(GlobalSet(bs.read_u32_leb128()?)),
        opcode if 0x28 <= opcode && opcode <= 0x3E => Ok(MemInstr(opcode, memarg(bs)?)),
        0x3F => {
            expect(bs, 0x00)?;
            Ok(MemSize)
        }
        0x40 => {
            expect(bs, 0x00)?;
            Ok(MemGrow)
        }
        0x41 => Ok(Const(Val::I32(bs.read_i32_leb128()?))),
        0x42 => Ok(Const(Val::I64(bs.read_i64_leb128()?))),
        0x43 => Ok(Const(Val::F32(bs.read_f32::<LittleEndian>()?))),
        0x44 => Ok(Const(Val::F64(bs.read_f64::<LittleEndian>()?))),
        opcode if 0x41 <= opcode && opcode <= 0xBF => Ok(NumInstr(opcode)),
        _other => {
            // FIXME:  Err(format_err!("unknown instr: 0x{:x}", other))
            Ok(Nop)
        }
    }
}

pub(crate) fn expr<R: Read>(bs: &mut BufReader<R>) -> Result<Vec<Instr>, Error> {
    let mut ins = Vec::new();

    while prefetch(bs)? != 0x0B {
        ins.push(instr(bs)?)
    }

    bs.consume(1);
    Ok(ins)
}
