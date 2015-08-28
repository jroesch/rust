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
extern crate build_helper;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use build_helper::{run, cc, ar, cflags};

fn main() {
    gcc::Config::new()
        .file("../rt/rust_builtin.c")
        .file("../rt/rust_android_dummy.c")
        .compile("librust_builtin.a");

    let target = env::var("TARGET").unwrap();
    if target.contains("linux") {
        build_libbacktrace(&target);

        if target.contains("musl") {
            println!("cargo:rustc-link-lib=static=unwind");
        } else {
            println!("cargo:rustc-link-lib=dl");
            println!("cargo:rustc-link-lib=rt");
            println!("cargo:rustc-link-lib=pthread");
            println!("cargo:rustc-link-lib=gcc_s");
        }
    } else if target.contains("android") {
        println!("cargo:rustc-link-lib=dl");
        println!("cargo:rustc-link-lib=log");
        println!("cargo:rustc-link-lib=gcc");
    } else if target.contains("freebsd") {
        println!("cargo:rustc-link-lib=execinfo");
        println!("cargo:rustc-link-lib=pthread");
        println!("cargo:rustc-link-lib=gcc_s");
    } else if target.contains("dragonfly") || target.contains("bitrig") ||
              target.contains("netbsd") || target.contains("openbsd") {
        println!("cargo:rustc-link-lib=pthread");

        if target.contains("netbsd") || target.contains("openbsd") {
            println!("cargo:rustc-link-lib=gcc");
        } else if target.contains("bitrig") {
            println!("cargo:rustc-link-lib=c++abi");
        } else if target.contains("dragonfly") {
            println!("cargo:rustc-link-lib=gcc_pic");
        }
    } else if target.contains("apple-darwin") {
        println!("cargo:rustc-link-lib=System");
    } else if target.contains("apple-ios") {
        println!("cargo:rustc-link-lib=System");
        println!("cargo:rustc-link-lib=objc");
        println!("cargo:rustc-link-lib=framework=Security");
        println!("cargo:rustc-link-lib=framework=Foundation");
    } else if target.contains("windows") {
        println!("cargo:rustc-link-lib=advapi32");
        println!("cargo:rustc-link-lib=ws2_32");
        println!("cargo:rustc-link-lib=userenv");
    }
}

fn build_libbacktrace(target: &str) {
    let src_dir = env::current_dir().unwrap().join("../libbacktrace");
    let build_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());

    println!("cargo:rustc-link-lib=static=backtrace");
    println!("cargo:rustc-link-search=native={}/.libs", build_dir.display());

    if fs::metadata(&build_dir.join(".libs/libbacktrace.a")).is_ok() {
        return
    }

    run(Command::new(src_dir.join("configure"))
                .current_dir(&build_dir)
                .arg("--with-pic")
                .arg("--disable-multilib")
                .arg("--disable-shared")
                .arg("--disable-host-shared")
                .arg(format!("--host={}", target))
                .env("CC", cc(target))
                .env("AR", ar(target))
                .env("RANLIB", format!("{} s", ar(target)))
                .env("CFLAGS", cflags(target).join(" ")));
    run(Command::new("make")
                .current_dir(&build_dir)
                .arg(format!("INCDIR={}", src_dir.display())));
}
