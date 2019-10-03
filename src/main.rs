#![allow(dead_code)]

use failure::Error;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};

use wasm_rt;

fn main() -> Result<(), Error> {
    env_logger::init();

    let _s = wasm_rt::store_init();

    let _args: Vec<String> = env::args().collect();
    let f = File::open("../wasm-game-of-life/pkg/wasm_game_of_life_bg.wasm")?;
    //let f = File::open(&args[1])?;
    let mut f = BufReader::new(f);
    let bs = f.fill_buf()?;

    let m = wasm_rt::module_decode(bs)?;

    println!("module imports: {:?}", wasm_rt::module_imports(&m));
    println!("module exports: {:?}", wasm_rt::module_exports(&m));

    //    let (_s, _m) = wasm_rt::module_instantiate(s, &m, &Vec::new())?;

    Ok(())
}
