// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate gcc;

use std::process::Command;
use std::env;
use std::path::PathBuf;

fn main() {
    let target = env::var("TARGET").unwrap();
    let llvm_config = env::var_os("LLVM_CONFIG").map(PathBuf::from)
                           .unwrap_or_else(|| {
        match env::var_os("CARGO_TARGET_DIR").map(PathBuf::from) {
            Some(dir) => {
                let to_test = dir.parent().unwrap().parent().unwrap()
                                 .join(&target).join("llvm/bin/llvm-config");
                if Command::new(&to_test).output().is_ok() {
                    return to_test
                }
            }
            None => {}
        }
        PathBuf::from("llvm-config")
    });

    // Link in our own LLVM shims, compiled with the same flags as LLVM
    let mut cmd = Command::new(&llvm_config);
    cmd.arg("--cxxflags");
    let cxxflags = output(&mut cmd);
    let mut cfg = gcc::Config::new();
    for flag in cxxflags.split_whitespace() {
        cfg.flag(flag);
    }
    cfg.file("../rustllvm/ExecutionEngineWrapper.cpp")
       .file("../rustllvm/PassWrapper.cpp")
       .file("../rustllvm/RustWrapper.cpp")
       .file("../rustllvm/ArchiveWrapper.cpp")
       .flag("-fno-rtti")
       .cpp(true)
       .cpp_link_stdlib(None) // we handle this below
       .compile("librustllvm.a");

    // Link in all LLVM libraries
    let mut cmd = Command::new(&llvm_config);
    cmd.arg("--libs").arg("--system-libs");
    for lib in output(&mut cmd).split_whitespace() {
        let name = if lib.starts_with("-l") {
            &lib[2..]
        } else if lib.starts_with("-") {
            &lib[1..]
        } else {
            continue
        };
        let kind = if name.starts_with("LLVM") {"static"} else {"dylib"};
        println!("cargo:rustc-link-lib={}={}", kind, name);
    }

    // LLVM ldflags
    let mut cmd = Command::new(&llvm_config);
    cmd.arg("--ldflags");
    for lib in output(&mut cmd).split_whitespace() {
        if lib.starts_with("-l") {
            println!("cargo:rustc-link-lib={}", &lib[2..]);
        } else if lib.starts_with("-L") {
            println!("cargo:rustc-link-search=native={}", &lib[2..]);
        }
    }

    // C++ runtime library
    if cfg!(feature = "static-libstdcpp") {
        assert!(!cxxflags.contains("stdlib=libc++"));
        println!("cargo:rustc-link-lib=static=stdc++");
    } else if !target.contains("msvc") {
        if cxxflags.contains("stdlib=libc++") {
            println!("cargo:rustc-link-lib=c++");
        } else {
            println!("cargo:rustc-link-lib=stdc++");
        }
    }
}

fn output(cmd: &mut Command) -> String {
    println!("running {:?}", cmd);
    let output = cmd.output().unwrap();
    if !output.status.success() {
        panic!("expected success, got: {}", output.status);
    }
    String::from_utf8(output.stdout).unwrap()
}
