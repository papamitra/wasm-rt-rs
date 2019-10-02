use super::alloc::{self, allocmodule, ExternVal, Store};
use super::module::{module, Module};
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
