#![allow(dead_code)]

use failure::Error;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};

use wasm_rt;
use wasm_rt::{func_invoke, ExternVal, ValType};

fn main() {
    env_logger::init();

    let s = wasm_rt::store_init();

    let _args: Vec<String> = env::args().collect();
    let f = File::open("../wasm-game-of-life/pkg/wasm_game_of_life_bg.wasm").unwrap();
    //let f = File::open(&args[1]).unwrap();
    let mut f = BufReader::new(f);
    let bs = f.fill_buf().unwrap();

    let m = wasm_rt::module_decode(bs).unwrap();

    println!("module imports: {:?}", wasm_rt::module_imports(&m));
    println!("module exports: {:?}", wasm_rt::module_exports(&m));

    let (s, funcaddr) = wasm_rt::func_alloc(
        s,
        &wasm_rt::FuncType(vec![ValType::I32, ValType::I32], vec![]),
        |stack, _store| {
            stack.pop();
            stack.pop();

            println!("hello, wasm");
            Ok(())
        },
    );

    let exvals = vec![ExternVal::Func(funcaddr)];
    let (s, _modinst) = wasm_rt::module_instantiate(s, &m, &exvals).unwrap();

    func_invoke(s, 1, &vec![]).unwrap();
}
