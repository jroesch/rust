// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// TODO:
//  * build rustdoc
//  * build rustbook
//  * build compiletest
//  * make dist
//  * generate docs
//  * external jemalloc
//  * configure options
//      * disable-docs
//      * enable-compiler-docs
//      * disable-optimize-tests
//      * llvm libc++
//      * local-rust
//      * static-stdcpp
//      * llvm-version-check
//      * android cross paths
//      * release-channel
//      * musl-root
//      * default-linker
//      * default-ar
//      * clang
//  * compiler selection bullshit
//  * NDK bullshit
//
//  * install options
//      * sysconfdir
//      * localstatedir
//      * datadir
//      * infodir
//      * prefix
//      * mandir
//      * dist-host-only
//      * install debugger scripts
//

#![deny(warnings)]

extern crate bootstrap;
extern crate build_helper;
extern crate cmake;
extern crate filetime;
extern crate getopts;
extern crate num_cpus;
extern crate rustc_serialize;
extern crate toml;

use std::collections::HashMap;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf, Component, Prefix};
use std::process::Command;

use build_helper::{run, run_silent, ar, cflags, cc, cxx};
use bootstrap::{dylib_path_var, dylib_path};
use filetime::FileTime;
use getopts::Options;

macro_rules! t {
    ($e:expr) => (match $e {
        Ok(e) => e,
        Err(e) => panic!("{} failed with {}", stringify!($e), e),
    })
}

struct Build {
    cargo: PathBuf,
    rustc: PathBuf,
    src: PathBuf,
    out: PathBuf,
    config: Config,
    skip_stage0: bool,
    skip_stage1: bool,
    skip_stage2: bool,
}

pub struct Config {
    ccache: bool,
    verbose: bool,
    submodules: bool,

    // llvm codegen options
    llvm_assertions: bool,
    llvm_optimize: bool,
    llvm_root: Option<PathBuf>,

    // rust codegen options
    rust_optimize: bool,
    rust_debug_assertions: bool,
    rust_debuginfo: bool,

    build: String,
    host: Vec<String>,
    target: Vec<String>,

    // libstd features
    debug_jemalloc: bool,
    elf_tls: bool,
    use_jemalloc: bool,
}

mod config;

fn main() {
    let mut opts = Options::new();
    opts.optflag("v", "verbose", "use verbose output");
    opts.optflag("", "skip-stage0", "skip the stage0 compiler step");
    opts.optflag("", "skip-stage1", "skip the stage1 compiler step");
    opts.optflag("", "skip-stage2", "skip the stage2 compiler step");
    opts.optopt("", "config", "TOML configuration file for build", "FILE");
    opts.optflag("h", "help", "print this help message");
    let m = opts.parse(&env::args().skip(1).collect::<Vec<_>>())
                .unwrap_or_else(|e| panic!("failed to parse options: {}", e));

    if m.opt_present("h") {
        let brief = format!("Usage: rust.py [options]");
        print!("{}", opts.usage(&brief));
        return
    }

    let mut build = Build {
        cargo: PathBuf::from(env("CARGO")),
        rustc: PathBuf::from(env("RUSTC")),
        src: PathBuf::from(env("SRC_DIR")),
        out: PathBuf::from(env("BUILD_DIR")),
        skip_stage0: false,
        skip_stage1: false,
        skip_stage2: false,
        config: Config {
            llvm_assertions: false,
            llvm_optimize: true,
            llvm_root: None,
            ccache: false,
            verbose: false,
            elf_tls: true,
            debug_jemalloc: false,
            use_jemalloc: true,
            submodules: false,
            rust_optimize: true,
            rust_debug_assertions: false,
            rust_debuginfo: false,
            build: env_s("BUILD"),
            host: Vec::new(),
            target: Vec::new(),
        },
    };
    let cfg_file = m.opt_str("config").or_else(|| {
        if fs::metadata("config.toml").is_ok() {
            Some("config.toml".to_string())
        } else {
            None
        }
    });
    if let Some(cfg) = cfg_file {
        config::configure(&mut build.config, &cfg);
    }
    if m.opt_present("v") {
        build.config.verbose = true;
    }
    build.skip_stage2 = m.opt_present("skip-stage2");
    build.skip_stage1 = build.skip_stage2 || m.opt_present("skip-stage1");
    build.skip_stage0 = build.skip_stage1 || m.opt_present("skip-stage0");
    build.build();
}

fn env(name: &str) -> OsString {
    env::var_os(name).unwrap_or_else(|| {
        panic!("must have env var `{}` defined", name)
    })
}

fn env_s(name: &str) -> String {
    env::var(name).unwrap_or_else(|_| {
        panic!("must have env var `{}` defined", name)
    })
}

enum Compiler<'a> {
    NightlySnapshot,
    Built(u32, &'a str),
}

impl Build {
    fn build(&self) {
        self.update_submodules();
        for host in self.config.host.iter() {
            self.build_llvm(host);
        }
        for target in self.config.target.iter() {
            self.build_compiler_rt(target);
        }
        if !self.skip_stage0 {
            self.build_stage(0, &self.config.build, &self.config.build,
                             &Compiler::NightlySnapshot);

            for host in self.config.host.iter() {
                if self.config.build != *host {
                    self.build_stage(0, host, host,
                                     &Compiler::Built(0, &self.config.build));
                }
            }
        }
        if !self.skip_stage1 {
            for host in self.config.host.iter() {
                self.build_stage(1, host, host, &Compiler::Built(0, host));
            }
        }
        if !self.skip_stage2 {
            for host in self.config.host.iter() {
                let compiler = Compiler::Built(1, host);
                for target in self.config.target.iter() {
                    if self.config.host.contains(target) {
                        self.build_stage(2, host, target, &compiler);
                    } else {
                        self.build_std(2, host, target, &compiler);
                    }
                }
            }
        }
    }

    fn update_submodules(&self) {
        if !self.config.submodules { return }
        self.run(Command::new("git").arg("submodule").arg("sync"));
        self.run(Command::new("git").arg("submodule").arg("init"));
        self.run(Command::new("git").arg("submodule").arg("update"));
        self.run(Command::new("git").arg("submodule").arg("update")
                                    .arg("--recursive"));
        self.run(Command::new("git").arg("submodule").arg("status")
                                    .arg("--recursive"));
        self.run(Command::new("git").arg("submodule").arg("foreach")
                                    .arg("--recursive")
                                    .arg("git").arg("clean").arg("-fdx"));
        self.run(Command::new("git").arg("submodule").arg("foreach")
                                    .arg("--recursive")
                                    .arg("git").arg("checkout").arg("."));
    }

    fn build_llvm(&self, target: &str) {
        if self.config.llvm_root.is_some() && target == self.config.build {
            return
        }
        let dst = self.llvm_out(target);
        let stamp = self.src.join("src/rustllvm/llvm-auto-clean-trigger");
        let llvm_config = dst.join("bin").join(self.exe("llvm-config", target));
        self.clear_if_dirty(&dst, &stamp, &llvm_config, || {});
        if fs::metadata(llvm_config).is_ok() {
            return
        }
        let _ = fs::remove_dir_all(&dst);
        t!(fs::create_dir_all(&dst));
        let assertions = if self.config.llvm_assertions {"ON"} else {"OFF"};

        let mut cfg = cmake::Config::new(self.src.join("src/llvm"));
        cfg.target(target)
           .out_dir(&dst)
           .define("CMAKE_INSTALL_PREFIX", &dst)
           .profile(if self.config.llvm_optimize {"Release"} else {"Debug"})
           .define("LLVM_ENABLE_ASSERTIONS", assertions)
           .define("LLVM_TARGETS_TO_BUILD", "X86;ARM;AArch64;Mips;PowerPC")
           .define("LLVM_INCLUDE_EXAMPLES", "OFF")
           .define("LLVM_INCLUDE_TESTS", "OFF")
           .define("LLVM_INCLUDE_DOCS", "OFF")
           .define("LLVM_ENABLE_ZLIB", "OFF")
           .define("WITH_POLLY", "OFF")
           .define("LLVM_ENABLE_TERMINFO", "OFF")
           .define("LLVM_ENABLE_LIBEDIT", "OFF");

        if target.contains("i686") && self.config.build.contains("x86_64") {
            cfg.define("LLVM_BUILD_32_BITS", "ON");
        }
        if self.config.ccache {
           cfg.define("CMAKE_C_COMPILER", "ccache")
              .define("CMAKE_C_COMPILER_ARG1", cc(target))
              .define("CMAKE_CXX_COMPILER", "ccache")
              .define("CMAKE_CXX_COMPILER_ARG1", cxx(target));
        } else {
           cfg.define("CMAKE_C_COMPILER", cc(target))
              .define("CMAKE_CXX_COMPILER", cxx(target));
        }

        if !target.contains("msvc") {
            cfg.build_arg("-j").build_arg(num_cpus::get().to_string());
        }
        cfg.build();
    }

    fn build_compiler_rt(&self, target: &str) {
        let dst = self.compiler_rt_out(target);
        let output = dst.join("triple/builtins/libcompiler_rt.a");
        if fs::metadata(&output).is_ok() {
            return
        }
        let src = self.src.join("src/compiler-rt");
        let unix_src = path2unix(&self.src.join("src/compiler-rt"));
        let unix_dst = path2unix(&dst);
        let mut cmd = Command::new("make");
        cmd.current_dir(&src)
           .arg(format!("ProjSrcRoot=/{}", unix_src))
           .arg(format!("ProjObjRoot=/{}", unix_dst))
           .arg(format!("CC={}", cc(target)))
           .arg(format!("CFLAGS={}", cflags(target).join(" ")))
           .arg(format!("AR={}", ar(target)))
           .arg(format!("RANLIB={} s", ar(target)))
           .arg(format!("TargetTriple={}", target))
           .arg("triple-builtins")
           .arg("-j").arg(num_cpus::get().to_string());
        run(&mut cmd);

        fn path2unix(p: &Path) -> String {
            p.components().filter_map(|c| {
                match c {
                    Component::Normal(p) => Some(p.to_str().unwrap().to_owned()),
                    Component::Prefix(p) => match p.kind() {
                        Prefix::Disk(d) => Some((d as char).to_string()),
                        _ => None,
                    },
                    _ => None,
                }
            }).collect::<Vec<_>>().join("/")
        }
    }

    fn build_stage(&self, stage: u32, sysroot_host: &str, target: &str,
                   compiler: &Compiler) {
        self.build_std(stage, sysroot_host, target, compiler);
        self.build_rustc(stage, sysroot_host, target, compiler);
    }

    /// Build the standard library.
    ///
    /// This will build the standard library for a particular stage of the build
    /// using the `compiler` targeting the `target` architecture. The artifacts
    /// created will also be linked into the `sysroot_host`'s sysroot directory.
    fn build_std(&self, stage: u32, sysroot_host: &str, target: &str,
                 compiler: &Compiler) {
        let host = self.compiler_host(compiler);

        // First up, build the standard library. Crates above the standard
        // library implicitly find the standard library in the sysroot and not
        // through Cargo, so after we're done here we start to assemble the
        // sysroot.
        let out_dir = self.stage_out(stage, &host, true);
        let shim = self.libstd_shim(stage, &host, target);
        let rustc = self.compiler(compiler);
        let libdir = self.sysroot_libdir(stage, sysroot_host, target);
        let _ = fs::remove_dir_all(&libdir);
        self.clear_if_dirty(&out_dir, &rustc, &shim, || {
            println!("Building stage{} std artifacts ({} -> {})", stage,
                     host, target);
            t!(fs::create_dir_all(&libdir));
            t!(fs::hard_link(self.compiler_rt_out(target)
                                 .join("triple/builtins/libcompiler_rt.a"),
                             libdir.join("libcompiler-rt.a")));
            let stage_arg = self.stage_arg(stage, compiler);
            let features = self.std_features(stage_arg, target);
            self.run(self.cargo(stage, compiler, &out_dir, sysroot_host, target)
                         .arg("--features").arg(features)
                         .arg("--lib")
                         .arg("--manifest-path")
                         .arg(self.src.join("src/rustc/Cargo.toml")));
        });
        self.add_to_sysroot(target, &out_dir, &libdir);
    }

    /// Build the compiler.
    ///
    /// This will build the compiler for a particular stage of the build using
    /// the `compiler` targeting the `target` architecture. The artifacts
    /// created will also be linked into the `sysroot_host`'s sysroot directory.
    /// If the `target` is the same as `sysroot_host`, then the compiler itself
    /// is linked into place.
    fn build_rustc(&self, stage: u32, sysroot_host: &str, target: &str,
                   compiler: &Compiler) {
        let host = self.compiler_host(compiler);
        // Now that our compiler is prepp'd to generate binaries for `target`,
        // run the build on the full compiler.
        let out_dir = self.stage_out(stage, &host, false);
        let fname = self.exe("rustc", target);
        let rustc = self.cargo_out(stage, &host, false, target).join(&fname);
        let shim = self.libstd_shim(stage, &host, target);
        self.clear_if_dirty(&out_dir, &shim, &rustc, || {
            println!("Building stage{} compiler artifacts ({} -> {})", stage,
                     host, target);
            let features = self.rustc_features(self.stage_arg(stage, compiler));
            let mut cargo = self.cargo(stage, compiler, &out_dir,
                                       sysroot_host, target);
            cargo.env("CFG_COMPILER_HOST_TRIPLE", target)
                 .arg("--features").arg(features)
                 .arg("--bin").arg("rustc")
                 .arg("--manifest-path")
                 .arg(self.src.join("src/rustc/Cargo.toml"));
            if target == self.config.build {
                if let Some(ref s) = self.config.llvm_root {
                    let cfg = self.exe("llvm-config", target);
                    cargo.env("LLVM_CONFIG", s.join("bin").join(cfg));
                }
            }
            self.run(&mut cargo);
        });
        t!(fs::create_dir_all(self.sysroot(stage, sysroot_host).join("bin")));
        let sysroot_libdir = self.sysroot_libdir(stage, sysroot_host, target);
        self.add_to_sysroot(target, &out_dir, &sysroot_libdir);

        if sysroot_host == target {
            self.assemble_compiler(stage, target, &host, &rustc);
        }
    }

    fn assemble_compiler(&self, stage: u32, host: &str, orig_host: &str,
                         rustc: &Path) {
        // Clear out old files
        let rustc_libdir = self.sysroot(stage, host).join(self.libdir(host));
        for f in t!(fs::read_dir(&rustc_libdir)).map(|f| t!(f)) {
            if !t!(f.file_type()).is_dir() {
                t!(fs::remove_file(f.path()));
            }
        }

        // Link in all built artifacts
        let sysroot_libdir = self.sysroot_libdir(stage, orig_host, host);
        for f in t!(fs::read_dir(&sysroot_libdir)).map(|f| t!(f)) {
            let f = f.path();
            let filename = f.file_name().unwrap().to_str().unwrap();
            if filename.ends_with(".rlib") || filename.ends_with(".a") ||
               filename.ends_with(".lib") {
                continue
            }
            t!(fs::hard_link(&f, rustc_libdir.join(filename)));
        }

        // Link the compiler binary itself into place
        let compiler = self.compiler(&Compiler::Built(stage, host));
        let _ = fs::remove_file(&compiler);
        t!(fs::hard_link(rustc, compiler));
    }

    /// Clear out `dir` if our build has been flagged as dirty, and also set
    /// ourselves as dirty if `file` changes when `f` is executed.
    fn clear_if_dirty<F: FnOnce()>(&self, dir: &Path,
                                   input: &Path, output: &Path, f: F) {
        if mtime(output) < mtime(input) && fs::metadata(output).is_ok() {
            self.verbose(&format!("Dirty - {}", output.display()));
            let _ = fs::remove_dir_all(dir);
        }
        f();
    }

    /// Prepares an invocation of `cargo` to be run.
    ///
    /// This will create a `Command` that represents a pending execution of
    /// Cargo for the specified stage, whether or not the standard library is
    /// being built, and using the specified compiler targeting `target`.
    fn cargo(&self, stage: u32, compiler: &Compiler, out_dir: &Path,
             sysroot_host: &str, target: &str) -> Command {
        let mut cargo = Command::new(&self.cargo);
        cargo.arg("build")
             .arg("--target").arg(target)
             .env("CARGO_TARGET_DIR", out_dir);

        // Customize the compiler we're running. Specify the compiler to cargo
        // as our shim and then pass it some various options used to configure
        // how the actual compiler itself is called.
        cargo.env("RUSTC", self.out.join("bootstrap/debug/rustc"))
             .env("RUSTC_REAL", self.compiler(compiler))
             .env("RUSTC_STAGE", self.stage_arg(stage, compiler).to_string())
             .env("RUSTC_DEBUGINFO", self.config.rust_debuginfo.to_string())
             .env("RUSTC_DEBUG_ASSERTIONS",
                  self.config.rust_debug_assertions.to_string())
             .env("RUSTC_SNAPSHOT", &self.rustc)
             .env("RUSTC_SYSROOT", self.sysroot(stage, &sysroot_host))
             .env("RUSTC_SNAPSHOT_LIBDIR", self.rustc_snapshot_libdir());

        // Specify some variuos options for build scripts used throughout the
        // build.
        cargo.env(format!("CC_{}", target), cc(target))
             .env(format!("AR_{}", target), ar(target));

        if self.config.verbose {
            cargo.arg("-v");
        }
        if self.config.rust_optimize {
            cargo.arg("--release");
        }
        self.set_rustc_lib_path(compiler, &mut cargo);
        return cargo
    }

    /// Cargo's output path for the standard library in a given stage, compiled
    /// by a particular compiler for the specified target.
    fn libstd_shim(&self, stage: u32, host: &str, target: &str) -> PathBuf {
        self.cargo_out(stage, host, true, target).join("libstd_shim.rlib")
    }

    /// Get a path to the compiler specified.
    fn compiler(&self, compiler: &Compiler) -> PathBuf {
        match *compiler {
            Compiler::NightlySnapshot => self.rustc.clone(),
            Compiler::Built(stage, host) => {
                self.sysroot(stage, host).join("bin")
                    .join(self.exe("rustc", host))
            }
        }
    }

    fn stage_arg(&self, stage: u32, compiler: &Compiler) -> u32 {
        match *compiler {
            Compiler::NightlySnapshot => stage,
            _ if stage == 0 => 1,
            _ => stage,
        }
    }

    /// Link some files into a rustc sysroot.
    ///
    /// For a particular stage this will link all of the contents of `out_dir`
    /// into the sysroot of the `host` compiler, assuming the artifacts are
    /// compiled for the specified `target`.
    fn add_to_sysroot(&self, target: &str, out_dir: &Path, sysroot_dst: &Path) {
        let out_dir = out_dir.join(target).join(self.cargo_dir());

        // Collect the set of all files in the dependencies directory, keyed
        // off the name of the library. We assume everything is of the form
        // `foo-<hash>.{rlib,so,...}`, and there could be multiple different
        // `<hash>` values for the same name (of old builds).
        let mut map = HashMap::new();
        for file in t!(fs::read_dir(out_dir.join("deps"))) {
            let file = t!(file).path();
            let filename = file.file_name().unwrap().to_str().unwrap();
            let dash = filename.find("-").unwrap();
            let key = (filename[..dash].to_string(),
                       file.extension().unwrap().to_owned());
            map.entry(key).or_insert(Vec::new())
               .push(file.clone());
        }

        // For all hash values found, pick the most recent one to move into the
        // sysroot, that should be the one we just built.
        for (_, paths) in map {
            let (_, path) = paths.iter().map(|path| {
                (mtime(&path).seconds(), path)
            }).max().unwrap();
            t!(fs::hard_link(&path,
                             sysroot_dst.join(path.file_name().unwrap())));
        }
    }

    /// Get the host triple for a particular compiler.
    fn compiler_host(&self, compiler: &Compiler) -> String {
        match *compiler {
            Compiler::NightlySnapshot => self.config.build.clone(),
            Compiler::Built(_, host) => host.to_string(),
        }
    }

    /// Get the space-separated set of activated features for the standard
    /// library.
    fn std_features(&self, stage: u32, target: &str) -> String {
        let stage_arg = if stage == 0 {"std-stage0"} else {"std-not-stage0"};
        let mut stage_arg = stage_arg.to_string();
        stage_arg.push_str(" build-std");
        if self.config.elf_tls {
            stage_arg.push_str(" elf-tls");
        }
        if self.config.debug_jemalloc {
            stage_arg.push_str(" debug-jemalloc");
        }
        if self.config.use_jemalloc && !target.contains("msvc") {
            stage_arg.push_str(" std-with-jemalloc");
        }
        return stage_arg
    }

    /// Get the space-separated set of activated features for the compiler.
    fn rustc_features(&self, stage: u32) -> String {
        let stage_arg = if stage == 0 {"rustc-stage0"} else {"rustc-not-stage0"};
        let mut stage_arg = stage_arg.to_string();
        stage_arg.push_str(" rustc");
        if self.config.use_jemalloc {
            stage_arg.push_str(" rustc-with-jemalloc");
        }
        return stage_arg
    }

    /// Component directory that Cargo will produce output into (e.g.
    /// release/debug)
    fn cargo_dir(&self) -> &'static str {
        if self.config.rust_optimize {"release"} else {"debug"}
    }

    fn sysroot(&self, stage: u32, host: &str) -> PathBuf {
        self.stage_out(stage, host, true).join("rustc")
    }

    fn sysroot_libdir(&self, stage: u32, host: &str, target: &str) -> PathBuf {
        self.sysroot(stage, host).join(self.libdir(host))
            .join("rustlib").join(target).join("lib")
    }

    /// Returns the root directory for all output generated in a particular
    /// stage when running with a particular host compiler.
    ///
    /// The `is_std` flag indicates whether the root directory is for the
    /// bootstrap of the standard library or for the compiler.
    fn stage_out(&self, stage: u32, host: &str, is_std: bool) -> PathBuf {
        self.out.join(host)
            .join(format!("stage{}{}", stage, if is_std {"-std"} else {""}))
    }

    /// Returns the root output directory for all Cargo output in a given stage,
    /// running a particular comipler, wehther or not we're building the
    /// standard library, and targeting the specified architecture.
    fn cargo_out(&self, stage: u32, host: &str, is_std: bool,
                 target: &str) -> PathBuf {
        self.stage_out(stage, host, is_std).join(target).join(self.cargo_dir())
    }

    /// Root output directory for LLVM compiled for `target`
    fn llvm_out(&self, target: &str) -> PathBuf {
        self.out.join(target).join("llvm")
    }

    /// Root output directory for compiler-rt compiled for `target`
    fn compiler_rt_out(&self, target: &str) -> PathBuf {
        self.out.join(target).join("compiler-rt")
    }

    fn set_rustc_lib_path(&self, compiler: &Compiler, cmd: &mut Command) {
        // Windows doesn't need dylib path munging because the dlls for the
        // compiler live next to the compiler and the system will find them
        // automatically.
        if cfg!(windows) { return }

        let mut path = dylib_path();
        path.insert(0, match *compiler {
            Compiler::NightlySnapshot => self.rustc_snapshot_libdir(),
            Compiler::Built(stage, host) => self.sysroot(stage, host).join("lib"),
        });
        cmd.env(dylib_path_var(), t!(env::join_paths(path)));
    }

    fn rustc_snapshot_libdir(&self) -> PathBuf {
        self.rustc.parent().unwrap().parent().unwrap()
            .join(self.libdir(&self.config.build))
    }

    fn libdir(&self, target: &str) -> &'static str {
        if target.contains("windows") {"bin"} else {"lib"}
    }

    /// Given an executable called `name`, return the filename for the
    /// executable for a particular target.
    fn exe(&self, name: &str, target: &str) -> String {
        if target.contains("windows") {
            format!("{}.exe", name)
        } else {
            name.to_string()
        }
    }

    fn run(&self, cmd: &mut Command) {
        self.verbose(&format!("running: {:?}", cmd));
        run_silent(cmd)
    }

    fn verbose(&self, msg: &str) {
        if self.config.verbose {
            println!("{}", msg);
        }
    }
}

fn mtime(path: &Path) -> FileTime {
    fs::metadata(path).map(|f| {
        FileTime::from_last_modification_time(&f)
    }).unwrap_or(FileTime::zero())
}
