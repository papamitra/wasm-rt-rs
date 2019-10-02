use super::alloc::{self, allocmodule, ExternVal, Store};
use super::module::{module, ExportDesc, ExternType, ImportDesc, Module};
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
            let externval = match im.desc {
                ImportDesc::Func(x) => ExternType::Func(m.types[x as usize].clone()),
                ImportDesc::Table(x) => ExternType::Table(m.tables[x as usize].clone()),
                ImportDesc::Mem(x) => ExternType::Mem(m.mems[x as usize].clone()),
                ImportDesc::Global(x) => {
                    ExternType::Global(m.globals[x as usize].globaltype.clone())
                }
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
                ExportDesc::Func(x) => ExternType::Func(m.types[x as usize].clone()),
                ExportDesc::Table(x) => ExternType::Table(m.tables[x as usize].clone()),
                ExportDesc::Mem(x) => ExternType::Mem(m.mems[x as usize].clone()),
                ExportDesc::Global(x) => {
                    ExternType::Global(m.globals[x as usize].globaltype.clone())
                }
            };

            (ex.name.clone(), externval)
        })
        .collect()
}
