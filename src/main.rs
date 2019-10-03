#![allow(dead_code)]

use failure::Error;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};

use wasm_rt;
use wasm_rt::{ExternVal, ValType};

fn main() -> Result<(), Error> {
    env_logger::init();

    let s = wasm_rt::store_init();

    let _args: Vec<String> = env::args().collect();
    let f = File::open("../wasm-game-of-life/pkg/wasm_game_of_life_bg.wasm")?;
    //let f = File::open(&args[1])?;
    let mut f = BufReader::new(f);
    let bs = f.fill_buf()?;

    let m = wasm_rt::module_decode(bs)?;

    println!("module imports: {:?}", wasm_rt::module_imports(&m));
    println!("module exports: {:?}", wasm_rt::module_exports(&m));

    //    let (_s, _m) = wasm_rt::module_instantiate(s, &m, &Vec::new())?;

    let (s, funcaddr) = wasm_rt::func_alloc(
        s,
        &wasm_rt::FuncType(vec![ValType::I32, ValType::I32], vec![]),
        |stack, store| {
            stack.pop();
            stack.pop();

            println!("hello, wasm");
            Ok(())
        },
    );

    let exvals = vec![ExternVal::Func(funcaddr)];
    let (s, modinst) = wasm_rt::module_instantiate(s, &m, &exvals)?;

    Ok(())
}
