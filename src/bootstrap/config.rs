use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::process;

use num_cpus;
use rustc_serialize::Decodable;
use toml::{Parser, Decoder, Value};

use Config;

#[derive(RustcDecodable)]
struct TomlConfig {
    build: Build,
    llvm: Option<Llvm>,
    rust: Option<Rust>,
}

#[derive(RustcDecodable)]
struct Build {
    build: Option<String>,
    host: Vec<String>,
    target: Vec<String>,
}

#[derive(RustcDecodable)]
struct Llvm {
    ccache: Option<bool>,
    assertions: Option<bool>,
    optimize: Option<bool>,
    root: Option<String>,
}

#[derive(RustcDecodable)]
struct Rust {
    elf_tls: Option<bool>,
    optimize: Option<bool>,
    codegen_units: Option<u32>,
    debug_assertions: Option<bool>,
    debuginfo: Option<bool>,
    debug_jemalloc: Option<bool>,
    use_jemalloc: Option<bool>,
    default_linker: Option<String>,
    default_ar: Option<String>,
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

    set(&mut config.build, toml.build.build.clone());
    config.host.push(config.build.clone());
    for host in toml.build.host.iter() {
        config.host.push(host.clone());
    }
    for target in config.host.iter().chain(&toml.build.target) {
        config.target.push(target.clone());
    }
    if let Some(ref llvm) = toml.llvm {
        set(&mut config.ccache, llvm.ccache);
        set(&mut config.llvm_assertions, llvm.assertions);
        set(&mut config.llvm_optimize, llvm.optimize);
        set(&mut config.llvm_optimize, llvm.optimize);

        if let Some(ref s) = llvm.root {
            config.llvm_root = Some(env::current_dir().unwrap().join(s));
        }
    }
    if let Some(ref rust) = toml.rust {
        set(&mut config.elf_tls, rust.elf_tls);
        set(&mut config.rust_debug_assertions, rust.debug_assertions);
        set(&mut config.rust_debuginfo, rust.debuginfo);
        set(&mut config.rust_optimize, rust.optimize);
        set(&mut config.debug_jemalloc, rust.debug_jemalloc);
        set(&mut config.use_jemalloc, rust.use_jemalloc);
        config.rustc_default_linker = rust.default_linker.clone();
        config.rustc_default_ar = rust.default_ar.clone();

        match rust.codegen_units {
            Some(0) => config.rust_codegen_units = num_cpus::get() as u32,
            Some(n) => config.rust_codegen_units = n,
            None => {}
        }
    }
}

fn set<T>(field: &mut T, val: Option<T>) {
    if let Some(v) = val {
        *field = v;
    }
}
