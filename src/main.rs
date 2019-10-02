#![allow(dead_code)]

use failure::Error;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};

use wasm_rt;

fn main() -> Result<(), Error> {
    env_logger::init();

    let s = wasm_rt::store_init();

    let args: Vec<String> = env::args().collect();
    //    let f = File::open("../wasm-game-of-life/pkg/wasm_game_of_life_bg.wasm")?;
    let f = File::open(&args[1])?;
    let mut f = BufReader::new(f);
    let bs = f.fill_buf()?;

    let m = wasm_rt::module_decode(bs)?;

    let (_s, _m) = wasm_rt::module_instantiate(s, &m, &Vec::new())?;

    /*    env_logger::init();

        let args: Vec<String> = env::args().collect();

        //debug!("read wasm: {}", args[1]);

        let f = File::open("../wasm-game-of-life/pkg/wasm_game_of_life_bg.wasm")?;
        let mut reader = BufReader::new(f);

        let _md = module::module(&mut reader)?;

        //    let mut store = alloc::Store::new();

        //    alloc::allocmodule(&mut store, &md, &Vec::new(), &Vec::new())?;

        //    instruction::instr(&mut BufReader::new(&mut vec![0u8].as_slice()));
    */
    Ok(())
}
