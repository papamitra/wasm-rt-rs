use super::execution::{eval_expr, invoke, Frame, StackEntry};
use super::module::*;
use failure::{format_err, Error};
use log::debug;
use std::cell::RefCell;
use std::convert::{Into, TryFrom};
use std::rc::Rc;
pub type FuncAddr = usize;
type TableAddr = usize;
type MemAddr = usize;
type GlobalAddr = usize;

#[derive(Debug)]
pub(crate) struct ExportInst {
    pub(crate) name: String,
    pub(crate) value: ExternVal,
}

#[derive(Debug)]
pub struct ModInst {
    pub(crate) types: Vec<FuncType>,
    pub(crate) funcs: Vec<FuncAddr>,
    pub(crate) tables: Vec<TableAddr>,
    pub(crate) mems: Vec<MemAddr>,
    pub(crate) globals: Vec<GlobalAddr>,
    pub(crate) exports: Vec<ExportInst>,
}

impl ModInst {
    pub(crate) fn new() -> Self {
        ModInst {
            types: Vec::new(),
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub enum ExternVal {
    Func(FuncAddr),
    Table(TableAddr),
    Mem(MemAddr),
    Global(GlobalAddr),
}

fn extern_funcs(externvals: &[ExternVal]) -> Vec<FuncAddr> {
    use ExternVal::*;
    externvals
        .iter()
        .filter_map(|v| match v {
            Func(f) => Some(*f),
            _ => None,
        })
        .collect()
}

fn extern_tables(externvals: &[ExternVal]) -> Vec<TableAddr> {
    use ExternVal::*;
    externvals
        .iter()
        .filter_map(|v| match v {
            Table(t) => Some(*t),
            _ => None,
        })
        .collect()
}

fn extern_mems(externvals: &[ExternVal]) -> Vec<MemAddr> {
    use ExternVal::*;
    externvals
        .iter()
        .filter_map(|v| match v {
            Mem(m) => Some(*m),
            _ => None,
        })
        .collect()
}

fn extern_globals(externvals: &[ExternVal]) -> Vec<GlobalAddr> {
    use ExternVal::*;
    externvals
        .iter()
        .filter_map(|v| match v {
            Global(g) => Some(*g),
            _ => None,
        })
        .collect()
}

#[derive(PartialEq, Clone, Debug)]
pub(crate) enum Val {
    I32(u32),
    I64(u64),
    F32(f32),
    F64(f64),
}

impl TryFrom<Val> for u32 {
    type Error = failure::Error;
    fn try_from(val: Val) -> Result<u32, Self::Error> {
        match val {
            Val::I32(v) => Ok(v),
            _ => Err(format_err!("type mismatch").into()),
        }
    }
}

impl Into<Val> for u32 {
    fn into(self) -> Val {
        Val::I32(self)
    }
}

impl TryFrom<Val> for i32 {
    type Error = failure::Error;
    fn try_from(val: Val) -> Result<i32, Self::Error> {
        match val {
            Val::I32(v) => Ok(v as i32),
            _ => Err(format_err!("type mismatch").into()),
        }
    }
}

impl Into<Val> for i32 {
    fn into(self) -> Val {
        Val::I32(self as u32)
    }
}

impl TryFrom<Val> for u64 {
    type Error = failure::Error;
    fn try_from(val: Val) -> Result<u64, Self::Error> {
        match val {
            Val::I64(v) => Ok(v),
            _ => Err(format_err!("type mismatch").into()),
        }
    }
}

impl Into<Val> for u64 {
    fn into(self) -> Val {
        Val::I64(self)
    }
}

impl TryFrom<Val> for i64 {
    type Error = failure::Error;
    fn try_from(val: Val) -> Result<i64, Self::Error> {
        match val {
            Val::I64(v) => Ok(v as i64),
            _ => Err(format_err!("type mismatch").into()),
        }
    }
}

impl Into<Val> for i64 {
    fn into(self) -> Val {
        Val::I64(self as u64)
    }
}

impl TryFrom<Val> for f32 {
    type Error = failure::Error;
    fn try_from(val: Val) -> Result<f32, Self::Error> {
        match val {
            Val::F32(v) => Ok(v),
            _ => Err(format_err!("type mismatch").into()),
        }
    }
}

impl Into<Val> for f32 {
    fn into(self) -> Val {
        Val::F32(self)
    }
}

impl TryFrom<Val> for f64 {
    type Error = failure::Error;
    fn try_from(val: Val) -> Result<f64, Self::Error> {
        match val {
            Val::F64(v) => Ok(v),
            _ => Err(format_err!("type mismatch").into()),
        }
    }
}

impl Into<Val> for f64 {
    fn into(self) -> Val {
        Val::F64(self)
    }
}

#[derive(Debug)]
pub(crate) struct WasmFuncInst {
    pub(crate) functype: FuncType,
    pub(crate) modinst: Rc<RefCell<ModInst>>,
    pub(crate) code: Func,
}

#[derive(Debug)]
pub(crate) enum FuncInst {
    WasmFuncInst(WasmFuncInst),
    HostFuncInst,
}

#[derive(Debug)]
pub(crate) struct GlobalInst {
    pub(crate) val: Val,
    pub(crate) mutabl: Mut,
}

#[derive(Debug)]
pub struct Store {
    pub(crate) funcs: Vec<FuncInst>,
    pub(crate) tables: Vec<TableInst>,
    pub(crate) mems: Vec<MemInst>,
    pub(crate) globals: Vec<GlobalInst>,
}

impl Store {
    pub(crate) fn new() -> Self {
        Store {
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct TableInst {
    pub(crate) elems: Vec<Option<FuncAddr>>,
    max: u32,
}

#[derive(Debug)]
pub(crate) struct MemInst {
    pub(crate) data: Vec<u8>,
    pub(crate) max: u32,
}

pub(crate) fn allocmodule(
    s: &mut Store,
    m: &Module,
    externvals: &[ExternVal],
    vals: &[Val],
) -> Result<Rc<RefCell<ModInst>>, Error> {
    let modinst = Rc::new(RefCell::new(ModInst::new()));
    modinst.borrow_mut().types = m.types.clone();

    modinst
        .borrow_mut()
        .funcs
        .append(&mut extern_funcs(externvals));

    modinst
        .borrow_mut()
        .tables
        .append(&mut extern_tables(externvals));

    modinst
        .borrow_mut()
        .mems
        .append(&mut extern_mems(externvals));

    modinst
        .borrow_mut()
        .globals
        .append(&mut extern_globals(externvals));

    for func in m.funcs.iter() {
        let funcaddr = allocfunc(s, &func, &modinst, m)?;
        modinst.borrow_mut().funcs.push(funcaddr);
    }

    for table in m.tables.iter() {
        let tableaddr = alloctable(s, table)?;
        modinst.borrow_mut().tables.push(tableaddr);
    }

    for mem in m.mems.iter() {
        let memaddr = allocmem(s, mem)?;
        modinst.borrow_mut().mems.push(memaddr);
    }

    for (i, global) in m.globals.iter().enumerate() {
        let val = vals.get(i).ok_or(format_err!(
            "allocmodule failed: vals[{}] is out of bounds",
            i
        ))?;
        let globaladdr = allocglobal(s, &global.globaltype, &val)?;
        modinst.borrow_mut().globals.push(globaladdr);
    }

    for export in m.exports.iter() {
        let v = match export.desc {
            ExportDesc::Func(x) => ExternVal::Func(*modinst.borrow().funcs.get(x as usize).ok_or(
                format_err!("allocmodule failed: funcaddr[{}] is out of bounds", x),
            )?),
            ExportDesc::Table(x) => {
                ExternVal::Table(*modinst.borrow().tables.get(x as usize).ok_or(format_err!(
                    "allocmodule failed: tableaddr[{}] is out of bounds",
                    x
                ))?)
            }

            ExportDesc::Mem(x) => ExternVal::Mem(*modinst.borrow().mems.get(x as usize).ok_or(
                format_err!("allocmodule failed: memaddr[{}] is out of bounds", x),
            )?),
            ExportDesc::Global(x) => {
                ExternVal::Global(*modinst.borrow().globals.get(x as usize).ok_or(format_err!(
                    "allocmodule failed: globaladdr[{}] is out of bounds",
                    x
                ))?)
            }
        };

        modinst.borrow_mut().exports.push(ExportInst {
            name: export.name.clone(),
            value: v,
        });
    }

    Ok(modinst)
}

fn allocfunc(
    s: &mut Store,
    func: &Func,
    modinst: &Rc<RefCell<ModInst>>,
    m: &Module,
) -> Result<FuncAddr, Error> {
    let addr = s.funcs.len();

    let ftype = match modinst.borrow().types.get(func.typeidx as usize) {
        Some(t) => t.clone(),
        _ => return Err(format_err!("allocfunc: invalid typeindex {}", func.typeidx)),
    };

    s.funcs.push(FuncInst::WasmFuncInst(WasmFuncInst {
        functype: ftype,
        modinst: modinst.clone(),
        code: func.clone(),
    }));
    Ok(addr)
}

fn alloctable(s: &mut Store, tabletype: &TableType) -> Result<TableAddr, Error> {
    use TableType::*;

    let addr = s.tables.len();
    match tabletype {
        FuncRef(Limits(n, m)) => s.tables.push(TableInst {
            elems: vec![None; *n as usize],
            max: *m,
        }),
    }

    Ok(addr)
}

fn allocmem(s: &mut Store, limits: &Limits) -> Result<MemAddr, Error> {
    let addr = s.mems.len();
    let Limits(n, m) = limits;
    s.mems.push(MemInst {
        data: vec![0; (n * 64 * 1024) as usize],
        max: *m,
    });
    Ok(addr)
}

fn allocglobal(s: &mut Store, globaltype: &GlobalType, val: &Val) -> Result<GlobalAddr, Error> {
    let addr = s.globals.len();
    s.globals.push(GlobalInst {
        mutabl: globaltype.mutabl.clone(),
        val: val.clone(),
    });
    Ok(addr)
}

fn instantiate(
    store: &mut Store,
    module: &Module,
    externvals: &[ExternVal],
) -> Result<Rc<RefCell<ModInst>>, Error> {
    let mut global_vals = globals_init(store, module, externvals)?;

    let modinst = allocmodule(store, module, externvals, &global_vals)?;

    let f = Frame::new_with(0, Vec::new(), modinst.clone());
    let mut stack = Vec::new();

    stack.push(StackEntry::Frame(Rc::new(RefCell::new(f))));

    // Verify elems (but store is updated)
    for elem in module.elems.iter() {
        let eo = match eval_expr(&mut stack, store, &elem.offset)? {
            Val::I32(eo) => eo as usize,
            _ => return Err(format_err!("instantiate failed: elem.offset calc failed")),
        };

        let tableidx = elem.table as usize;
        let tableaddr = *modinst.borrow().tables.get(tableidx).ok_or(format_err!(
            "instantiate failed: modinst.tables[{}] is out of bounds",
            tableidx
        ))? as usize;

        let tableinst = store.tables.get_mut(tableaddr).ok_or(format_err!(
            "instantiate failed: s.tables[{}] is out of bounds",
            tableaddr
        ))?;

        let eend = eo + elem.init.len();

        if eend > tableinst.elems.len() {
            return Err(format_err!(
                "instantiate failed: eend > tableinst.elem length"
            ));
        }

        // instantiate step 14.
        for (j, funcidx) in elem.init.iter().enumerate() {
            let funcaddr = *modinst
                .borrow()
                .funcs
                .get(*funcidx as usize)
                .ok_or(format_err!(
                    "instantiate failed: modinst.funcaddrs[{}] is not exist",
                    funcidx
                ))?;
            tableinst.elems[eo + j] = Some(funcaddr);
        }
    }

    // Verify datas (but store is updated)
    for data in module.datas.iter() {
        let doffset = match eval_expr(&mut stack, store, &data.offset)? {
            Val::I32(doffset) => doffset as usize,
            _ => return Err(format_err!("instantiate failed: data.offset calc failed")),
        };

        let memidx = data.data as usize;
        let memaddr = *modinst.borrow().mems.get(memidx).ok_or(format_err!(
            "instantiate failed: modinst.mems[{}] is out of bounds",
            memidx
        ))? as usize;

        let meminst = store.mems.get_mut(memaddr).ok_or(format_err!(
            "instantiate failed: s.mems[{}] is out of bounds",
            memaddr
        ))?;

        let dend = doffset + data.init.len();

        if dend > meminst.data.len() {
            return Err(format_err!(
                "instantiate failed: dend > meminst.data length"
            ));
        }

        for (j, b) in data.init.iter().enumerate() {
            meminst.data[doffset + j] = *b;
        }
    }

    match stack.pop() {
        Some(StackEntry::Frame(_)) => {}
        _ => return Err(format_err!("instantiate failed: Verify failed")),
    }

    if let Some(funcidx) = module.start {
        let funcaddr = *modinst
            .borrow()
            .funcs
            .get(funcidx as usize)
            .ok_or(format_err!(
                "instantiate failed: start function(funcidx = {}) is not found",
                funcidx
            ))?;

        invoke(funcaddr, &mut stack, store)?;
    }

    Ok(modinst)
}

fn globals_init(
    store: &mut Store,
    module: &Module,
    externvals: &[ExternVal],
) -> Result<Vec<Val>, Error> {
    let modinst_aux = {
        let mut m = ModInst::new();
        m.globals = extern_globals(externvals);
        Rc::new(RefCell::new(m))
    };

    let frame_aux = Rc::new(RefCell::new(Frame::new_with(0, Vec::new(), modinst_aux)));

    // Should use new one?
    let mut stack = Vec::new();
    stack.push(StackEntry::Frame(frame_aux));

    let mut vals = Vec::new();
    for global in module.globals.iter() {
        vals.push(eval_expr(&mut stack, store, &global.init)?);
    }

    Ok(vals)
}
