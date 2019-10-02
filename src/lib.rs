#![allow(dead_code)]

mod alloc;
mod api;
mod execution;
mod instruction;
mod leb128;
mod module;

pub use self::alloc::ExternVal;
pub use self::api::{module_decode, module_instantiate, store_init, ModInst};
