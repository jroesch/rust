use std::fs::File;
use std::io::prelude::*;
use std::process;

use rustc_serialize::Decodable;
use toml::{Parser, Decoder, Value};

use Config;

#[derive(RustcDecodable)]
struct TomlConfig {
    llvm: Option<Llvm>,
    rust: Option<Rust>,
}

#[derive(RustcDecodable)]
struct Llvm {
    ccache: Option<bool>,
    assertions: Option<bool>,
    optimize: Option<bool>,
}

#[derive(RustcDecodable)]
struct Rust {
    elf_tls: Option<bool>,
    optimize: Option<bool>,
    debug_assertions: Option<bool>,
    debuginfo: Option<bool>,
    debug_jemalloc: Option<bool>,
    use_jemalloc: Option<bool>,
}

pub fn configure(config: &mut Config, file: &str) {
    let mut f = t!(File::open(&file));
    let mut toml = String::new();
    t!(f.read_to_string(&mut toml));
    let mut p = Parser::new(&toml);
    let table = match p.parse() {
        Some(table) => table,
        None => {
            println!("failed to parse TOML configuration:");
            for err in p.errors.iter() {
                let (loline, locol) = p.to_linecol(err.lo);
                let (hiline, hicol) = p.to_linecol(err.hi);
                println!("{}:{}-{}:{}: {}", loline, locol, hiline, hicol,
                         err.desc);
            }
            process::exit(2);
        }
    };
    let mut d = Decoder::new(Value::Table(table));
    let toml: TomlConfig = match Decodable::decode(&mut d) {
        Ok(cfg) => cfg,
        Err(e) => {
            println!("failed to decode TOML: {}", e);
            process::exit(2);
        }
    };

    if let Some(ref llvm) = toml.llvm {
        set(&mut config.ccache, llvm.ccache);
        set(&mut config.llvm_assertions, llvm.assertions);
        set(&mut config.llvm_optimize, llvm.optimize);
    }
    if let Some(ref rust) = toml.rust {
        set(&mut config.elf_tls, rust.elf_tls);
        set(&mut config.rust_debug_assertions, rust.debug_assertions);
        set(&mut config.rust_debuginfo, rust.debuginfo);
        set(&mut config.rust_optimize, rust.optimize);
        set(&mut config.debug_jemalloc, rust.debug_jemalloc);
        set(&mut config.use_jemalloc, rust.use_jemalloc);
    }
}

fn set<T: Copy>(field: &mut T, val: Option<T>) {
    if let Some(v) = val {
        *field = v;
    }
}
