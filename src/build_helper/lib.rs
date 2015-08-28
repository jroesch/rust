// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::process::Command;

pub fn run(cmd: &mut Command) {
    println!("running: {:?}", cmd);
    run_silent(cmd);
}

pub fn run_silent(cmd: &mut Command) {
    let status = match cmd.status() {
        Ok(status) => status,
        Err(e) => fail(&format!("failed to execute command: {}", e)),
    };
    if !status.success() {
        fail(&format!("command did not execute successfully, got: {}", status));
    }
}

pub fn cc(target: &str) -> String {
    if target.contains("windows") {
        "gcc".to_string()
    } else if let Some(prefix) = cross_prefix(target) {
        format!("{}-gcc", prefix)
    } else {
        "cc".to_string()
    }
}

pub fn cflags(target: &str) -> Vec<String> {
    if target.contains("windows") {
        Vec::new()
    } else {
        let mut flags = Vec::new();
        if target.contains("i686") {
            flags.push("-m32".to_string());
        } else if target.contains("x86_64") {
            flags.push("-m64".to_string());
            flags.push("-fPIC".to_string());
        }
        return flags
    }
}

pub fn ar(target: &str) -> String {
    if let Some(prefix) = cross_prefix(target) {
        format!("{}-ar", prefix)
    } else {
        "ar".to_string()
    }
}

pub fn cxx(target: &str) -> String {
    if target.contains("windows") {
        "g++".to_string()
    } else {
        "c++".to_string()
    }
}

fn cross_prefix(target: &str) -> Option<&'static str> {
    match target {
        "arm-unknown-linux-gnueabihf" => Some("arm-linux-gnueabihf"),
        _ => None,
    }
}

fn fail(s: &str) -> ! {
    println!("\n\n{}\n\n", s);
    std::process::exit(1);
}
