use byteorder::ReadBytesExt;
use failure::format_err;
use failure::Error;
use log::debug;
use std::io::{BufReader, Read};

use super::alloc::Val;
use super::instruction::{expr, Instr};
use super::leb128::ReadLEB128Ext;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

impl ValType {
    pub(crate) fn zero_val(&self) -> Val {
        match self {
            ValType::I32 => Val::I32(0),
            ValType::I64 => Val::I64(0),
            ValType::F32 => Val::F32(0.0),
            ValType::F64 => Val::F64(0.0),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Limits(pub(crate) u32, pub(crate) u32); // min, max

#[derive(Debug, Clone)]
pub enum TableType {
    FuncRef(Limits),
}

type TypeIdx = usize;

#[derive(Debug)]
pub(crate) enum ImportDesc {
    Func(TypeIdx),
    Table(TableType),
    Mem(Limits),
    Global(GlobalType),
}

#[derive(Debug)]
pub(crate) struct Import {
    pub(crate) modname: String,
    pub(crate) name: String,
    pub(crate) desc: ImportDesc,
}

type FuncIdx = usize;
type TableIdx = usize;
type MemIdx = usize;
type GlobalIdx = usize;

#[derive(Debug)]
pub(crate) enum ExportDesc {
    Func(FuncIdx),
    Table(TableIdx),
    Mem(MemIdx),
    Global(GlobalIdx),
}

#[derive(Debug)]
pub(crate) struct Export {
    pub(crate) name: String,
    pub(crate) desc: ExportDesc,
}

#[derive(Debug, Clone)]
pub(crate) struct Func {
    pub(crate) typeidx: usize,
    pub(crate) locals: Vec<Locals>,
    pub(crate) expr: Vec<Instr>,
}

#[derive(Debug)]
pub struct Module {
    pub(crate) types: Vec<FuncType>,
    pub(crate) imports: Vec<Import>,
    pub(crate) tables: Vec<TableType>,
    pub(crate) mems: Vec<Limits>,
    pub(crate) globals: Vec<Global>,
    pub(crate) exports: Vec<Export>,
    pub(crate) start: Option<u32>,
    pub(crate) elems: Vec<Elem>,
    pub(crate) funcs: Vec<Func>,
    pub(crate) datas: Vec<Data>,
}

impl Module {
    fn new() -> Self {
        Module {
            types: Vec::new(),
            imports: Vec::new(),
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            start: None,
            elems: Vec::new(),
            datas: Vec::new(),
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub struct FuncType(pub Vec<ValType>, pub Vec<ValType>);

fn import<R>(r: &mut R) -> Result<Import, Error>
where
    R: Read,
{
    use ImportDesc::*;
    let modnm = name(r)?;
    let nm = name(r)?;
    let desc = match r.read_u8()? {
        0x00 => Func(r.read_u32_leb128()? as usize),
        0x01 => Table(tabletype(r)?),
        0x02 => Mem(limits(r)?),
        0x03 => Global(globaltype(r)?),
        n => return Err(format_err!("Invalid ImportDesc 0x{:x}", n)),
    };

    Ok(Import {
        modname: modnm,
        name: nm,
        desc: desc,
    })
}

fn export<R>(r: &mut R) -> Result<Export, Error>
where
    R: Read,
{
    use ExportDesc::*;
    let nm = name(r)?;
    let desc = match r.read_u8()? {
        0x00 => Func(r.read_u32_leb128()? as usize),
        0x01 => Table(r.read_u32_leb128()? as usize),
        0x02 => Mem(r.read_u32_leb128()? as usize),
        0x03 => Global(r.read_u32_leb128()? as usize),
        n => return Err(format_err!("Invalid ImportDesc 0x{:x}", n)),
    };

    Ok(Export {
        name: nm,
        desc: desc,
    })
}

pub(crate) fn valtype(v: u8) -> Result<ValType, Error> {
    use ValType::*;
    match v {
        0x7F => Ok(I32),
        0x7E => Ok(I64),
        0x7D => Ok(F32),
        0x7C => Ok(F64),
        _ => Err(format_err!("Invalid ValType: 0x{:x}", v)),
    }
}

fn functype<R>(r: &mut R) -> Result<FuncType, Error>
where
    R: Read,
{
    if r.read_u8()? != 0x60 {
        return Err(format_err!("Invalid FuncType"));
    }

    let t1n = r.read_u32_leb128()?;
    let t1 = (0..t1n)
        .map(|_| valtype(r.read_u8()?))
        .collect::<Result<Vec<_>, _>>()?;

    let t2n = r.read_u32_leb128()?;
    let t2 = (0..t2n)
        .map(|_| valtype(r.read_u8()?))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(FuncType(t1, t2))
}

fn name<R>(r: &mut R) -> Result<String, Error>
where
    R: Read,
{
    let n = r.read_u32_leb128()? as usize;
    let mut buf = vec![0; n];
    r.read_exact(&mut buf)?;
    Ok(String::from_utf8(buf)?)
}

fn limits<R>(r: &mut R) -> Result<Limits, Error>
where
    R: Read,
{
    match r.read_u8()? {
        0x00 => Ok(Limits(r.read_u32_leb128()?, std::u32::MAX)),
        0x01 => Ok(Limits(r.read_u32_leb128()?, r.read_u32_leb128()?)),
        _ => Err(format_err!("Invalid Limits")),
    }
}

fn tabletype<R>(r: &mut R) -> Result<TableType, Error>
where
    R: Read,
{
    if r.read_u8()? != 0x70 {
        return Err(format_err!("Invalid Table Element Type"));
    }

    Ok(TableType::FuncRef(limits(r)?))
}

#[derive(Clone, Debug)]
pub(crate) enum Mut {
    Const,
    Var,
}

#[derive(Debug, Clone)]
pub struct GlobalType {
    pub(crate) mutabl: Mut,
    pub(crate) valtype: ValType,
}

fn globaltype<R>(r: &mut R) -> Result<GlobalType, Error>
where
    R: Read,
{
    use Mut::*;

    let t = valtype(r.read_u8()?)?;
    let m = match r.read_u8()? {
        0x00 => Const,
        0x01 => Var,
        _ => return Err(format_err!("Invalid Mut type")),
    };

    Ok(GlobalType {
        mutabl: m,
        valtype: t,
    })
}

#[derive(Debug)]
pub(crate) struct Global {
    pub(crate) init: Vec<Instr>,
    pub(crate) globaltype: GlobalType,
}

fn global<R: Read>(r: &mut BufReader<R>) -> Result<Global, Error> {
    Ok(Global {
        globaltype: globaltype(r)?,
        init: expr(r)?,
    })
}

#[derive(Debug)]
pub(crate) struct Elem {
    pub(crate) table: u32,
    pub(crate) offset: Vec<Instr>,
    pub(crate) init: Vec<u32>,
}

fn elem<R: Read>(r: &mut BufReader<R>) -> Result<Elem, Error> {
    Ok(Elem {
        table: r.read_u32_leb128()?,
        offset: expr(r)?,
        init: (0..r.read_u32_leb128()?)
            .map(|_| r.read_u32_leb128())
            .collect::<Result<Vec<_>, _>>()?,
    })
}

#[derive(Clone, Debug)]
pub(crate) struct Locals(pub(crate) u32, pub(crate) ValType);

#[derive(Clone, Debug)]
pub(crate) struct Code {
    size: u32,
    pub(crate) locals: Vec<Locals>,
    pub(crate) expr: Vec<Instr>,
}

fn code<R: Read>(r: &mut BufReader<R>) -> Result<Code, Error> {
    let code = Code {
        size: r.read_u32_leb128()?,
        locals: vec(r, locals)?,
        expr: expr(r)?,
    };
    Ok(code)
}

fn locals<R: Read>(r: &mut BufReader<R>) -> Result<Locals, Error> {
    Ok(Locals(r.read_u32_leb128()?, valtype(r.read_u8()?)?))
}

#[derive(Debug)]
pub(crate) struct Data {
    pub(crate) data: u32,
    pub(crate) offset: Vec<Instr>,
    pub(crate) init: Vec<u8>,
}

fn data<R: Read>(r: &mut BufReader<R>) -> Result<Data, Error> {
    Ok(Data {
        data: r.read_u32_leb128()?,
        offset: expr(r)?,
        init: vec(r, |r| r.read_u8())?,
    })
}

#[derive(Debug)]
pub enum ExternType {
    Func(FuncType),
    Table(TableType),
    Mem(Limits),
    Global(GlobalType),
}

pub(crate) fn vec<R: Read, F, T, E>(r: &mut BufReader<R>, f: F) -> Result<Vec<T>, Error>
where
    F: Fn(&mut BufReader<R>) -> Result<T, E>,
    E: Into<Error>,
{
    let n = r.read_u32_leb128()?;
    (0..n)
        .map(|_| f(r).map_err(Into::into))
        .collect::<Result<Vec<T>, Error>>()
}

pub(crate) fn module<R>(r: &mut R) -> Result<Module, Error>
where
    R: Read,
{
    debug!("read magic");
    let mut magic = [0; 4];
    r.read_exact(&mut magic)?;
    if magic != *b"\0asm" {
        return Err(format_err!("bad magic"));
    }

    debug!("read version");
    let mut version = [0; 4];
    r.read_exact(&mut version)?;
    if version != [0x01, 0, 0, 0] {
        return Err(format_err!("unkonwn version: {:?}", version));
    }

    let mut m = Module::new();
    let mut funcs = Vec::new();

    loop {
        let secno = r.read_u8();
        if let Err(_) = secno {
            break;
        }
        let secno = secno.unwrap();
        debug!("secion number: {}", secno);

        let size = r.read_u32_leb128()? as usize;
        debug!("secion size: {}", size);
        let mut body = vec![0; size];
        r.read_exact(&mut body)?;

        let mut reader = BufReader::new(body.as_slice());

        match secno {
            0 => {
                debug!("custom section");
                match name(&mut reader) {
                    Ok(ref n) if *n == "name".to_string() => {
                        let subno = reader.read_u8()?;
                        let _subsize = reader.read_u32_leb128()?;

                        match subno {
                            0 => {
                                let modname = name(&mut reader)?;
                                println!("modname: {}", modname);
                            }
                            1 => {
                                println!("funcname");
                            }
                            2 => {
                                println!("localname");
                                // local names
                            }
                            _ => {
                                println!("unknown subno: {}", subno);
                            }
                        }
                    }
                    _ => {}
                }
            }
            1 => {
                debug!("type section");
                m.types.append(&mut vec(&mut reader, functype)?);
            }
            2 => {
                debug!("import section");
                m.imports.append(&mut vec(&mut reader, import)?);
            }
            3 => {
                debug!("function section");
                funcs.append(&mut vec(&mut reader, |r| {
                    r.read_u32_leb128().map(|x| x as usize)
                })?);
            }
            4 => {
                debug!("table section");
                m.tables.append(&mut vec(&mut reader, tabletype)?);
            }
            5 => {
                debug!("memory section");
                m.mems.append(&mut vec(&mut reader, limits)?);
            }
            6 => {
                debug!("global section");
                m.globals.append(&mut vec(&mut reader, global)?);
            }
            7 => {
                debug!("export section");
                m.exports.append(&mut vec(&mut reader, export)?);
            }
            8 => {
                debug!("start section");
                m.start = Some(reader.read_u32_leb128()?)
            }
            9 => {
                debug!("element section");
                m.elems.append(&mut vec(&mut reader, elem)?);
            }
            10 => {
                debug!("code section");
                m.funcs.append(
                    &mut vec(&mut reader, code)?
                        .into_iter()
                        .enumerate()
                        .map(|(i, c)| {
                            Ok(Func {
                                typeidx: *funcs.get(i).ok_or(format_err!(
                                    "module failed: funcs[{}] is out of bounds",
                                    i
                                ))?,
                                locals: c.locals,
                                expr: c.expr,
                            })
                        })
                        .collect::<Result<Vec<Func>, Error>>()?,
                );
            }
            11 => {
                debug!("data section");
                m.datas.append(&mut vec(&mut reader, data)?);
            }

            _ => return Err(format_err!("Invalid Section No: {}", secno)),
        }
    }

    Ok(m)
}
