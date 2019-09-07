#![allow(dead_code)]

use env_logger;
use failure::Error;
use log::debug;
use std::env;
use std::fs::File;
use std::io::BufReader;

mod alloc;
mod execution;
mod instruction;
mod leb128;
mod module;

fn main() -> Result<(), Error> {
    env_logger::init();

    let args: Vec<String> = env::args().collect();

    debug!("read wasm: {}", args[1]);

    let f = File::open(&args[1])?;
    let mut reader = BufReader::new(f);

    let md = module::module(&mut reader)?;

    let mut store = alloc::Store::new();

    alloc::allocmodule(&mut store, &md, &Vec::new(), &Vec::new())?;

    //    instruction::instr(&mut BufReader::new(&mut vec![0u8].as_slice()));
    Ok(())
}
