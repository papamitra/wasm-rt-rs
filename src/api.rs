use super::alloc::{self, allocmodule, ExternVal, FuncAddr, FuncInst, HostFuncInst, Store};
use super::execution::Stack;
use super::module::{module, ExportDesc, ExternType, FuncType, ImportDesc, Module};
use failure::Error;
use std::cell::RefCell;
use std::io::BufReader;
use std::rc::Rc;

pub type ModInst = Rc<RefCell<alloc::ModInst>>;

pub fn store_init() -> Store {
    Store::new()
}

pub fn module_decode(bs: &[u8]) -> Result<Module, Error> {
    let mut r = BufReader::new(bs);
    module(&mut r)
}

pub fn module_instantiate(
    s: Store,
    m: &Module,
    exvals: &[ExternVal],
) -> Result<(Store, ModInst), Error> {
    let mut s = s;
    let modinst = allocmodule(&mut s, m, exvals, &Vec::new())?;
    Ok((s, modinst))
}

pub fn module_imports(m: &Module) -> Vec<(String, String, ExternType)> {
    m.imports
        .iter()
        .map(|im| {
            let externval = match &im.desc {
                ImportDesc::Func(x) => ExternType::Func(m.types[*x].clone()),
                ImportDesc::Table(x) => ExternType::Table(x.clone()),
                ImportDesc::Mem(x) => ExternType::Mem(x.clone()),
                ImportDesc::Global(x) => ExternType::Global(x.clone()),
            };

            (im.modname.clone(), im.name.clone(), externval)
        })
        .collect()
}

pub fn module_exports(m: &Module) -> Vec<(String, ExternType)> {
    m.exports
        .iter()
        .map(|ex| {
            let externval = match ex.desc {
                ExportDesc::Func(x) => {
                    // Functions are referenced through function indices,
                    // starting with the smallest index not referencing a function import.
                    let idx = x - m.imports.len();
                    ExternType::Func(m.types[m.funcs[idx].typeidx].clone())
                }
                ExportDesc::Table(x) => ExternType::Table(m.tables[x].clone()),
                ExportDesc::Mem(x) => ExternType::Mem(m.mems[x].clone()),
                ExportDesc::Global(x) => ExternType::Global(m.globals[x].globaltype.clone()),
            };

            (ex.name.clone(), externval)
        })
        .collect()
}

pub fn func_alloc<F>(s: Store, functype: &FuncType, hostfunc: F) -> (Store, FuncAddr)
where
    F: Fn(&mut Stack, &mut Store) -> Result<(), Error> + 'static,
{
    let mut s = s;
    let funcaddr = s.funcs.len();

    s.funcs.push(FuncInst::HostFuncInst(HostFuncInst {
        functype: functype.clone(),
        func: Rc::new(RefCell::new(hostfunc)),
    }));

    (s, funcaddr)
}
