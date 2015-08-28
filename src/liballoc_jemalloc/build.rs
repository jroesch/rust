// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate build_helper;

use std::env;
use std::path::PathBuf;
use std::process::Command;
use build_helper::run;

fn main() {
    let target = env::var("TARGET").unwrap();
    let host = env::var("HOST").unwrap();
    let build_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let src_dir = env::current_dir().unwrap();

    let mut args = Vec::new();
    if target.contains("windows-gnu") {
        // This isn't necessarily a desired option, but it's harmless and
        // works around what appears to be a mingw-w64 bug.
        //
        // https://sourceforge.net/p/mingw-w64/bugs/395/
        args.push("--enable-lazy-lock".to_string());
    } else if target.contains("ios") || target.contains("android") {
        args.push("--disable-tls".to_string());
    }

    if cfg!(feature = "debug-jemalloc") {
        args.push("--enable-debug".to_string());
    }

    // Turn off broken quarantine (see jemalloc/jemalloc#161)
    args.push("--disable-fill".to_string());
    args.push("--with-jemalloc-prefix=je_".to_string());
    args.push(format!("--host={}", to_gnu(&target)));
    args.push(format!("--build={}", to_gnu(&host)));

    let configure = src_dir.join("../jemalloc/configure");
    run(Command::new("sh")
                .arg("-c").arg(format!("{} {}", configure.to_str().unwrap(),
                                       args.join(" "))
                                    .replace("C:\\", "/c/")
                                    .replace("\\", "/"))
                .current_dir(&build_dir)
                .env("CC", format!("{} {}", build_helper::cc(&target),
                                   build_helper::cflags(&target).join(" ")))
                .env("AR", build_helper::ar(&target))
                .env("RANLIB", format!("{} s", build_helper::ar(&target))));

    run(Command::new("make")
                .current_dir(&build_dir)
                .arg("build_lib_static"));

    if target.contains("windows") {
        println!("cargo:rustc-link-lib=static=jemalloc");
    } else {
        println!("cargo:rustc-link-lib=static=jemalloc_pic");
    }
    println!("cargo:rustc-link-search=native={}/lib", build_dir.display());
}

fn to_gnu(triple: &str) -> String {
    match triple {
        "i686-pc-windows-msvc" => "i686-pc-win32".to_string(),
        "x86_64-pc-windows-msvc" => "x86_64-pc-win32".to_string(),
        "i686-pc-windows-gnu" => "i686-w64-mingw32".to_string(),
        "x86_64-pc-windows-gnu" => "x86_64-w64-mingw32".to_string(),
        s => s.to_string(),
    }
}
