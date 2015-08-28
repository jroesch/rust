# Copyright 2015 The Rust Project Developers. See the COPYRIGHT
# file at the top-level directory of this distribution and at
# http://rust-lang.org/COPYRIGHT.
#
# Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
# http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
# <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
# option. This file may not be copied, modified, or distributed
# except according to those terms.

import download
import os
import subprocess
import sys

class RustBuild:
    def download_rust_nightly(self):
        cache_dst = os.path.join(self.build_dir, self.build, "cache")
        rustc_cache = os.path.join(cache_dst, self.snap_rustc_date())
        cargo_cache = os.path.join(cache_dst, self.snap_cargo_date())
        if not os.path.exists(rustc_cache):
            os.makedirs(rustc_cache)
        if not os.path.exists(cargo_cache):
            os.makedirs(cargo_cache)

        if not os.path.exists(self.rustc()):
            filename = "rustc-nightly-" + self.build + ".tar.gz"
            url = "https://static.rust-lang.org/dist/" + self.snap_rustc_date()
            tarball = os.path.join(rustc_cache, filename)
            if not os.path.exists(tarball):
                download.get(url + "/" + filename, tarball)
            download.unpack(tarball, self.rustc_root())

        if not os.path.exists(self.cargo()):
            filename = "cargo-nightly-" + self.build + ".tar.gz"
            url = "https://static.rust-lang.org/cargo-dist/" + self.snap_cargo_date()
            tarball = os.path.join(cargo_cache, filename)
            if not os.path.exists(tarball):
                download.get(url + "/" + filename, tarball)
            download.unpack(tarball, self.cargo_root())

    def snap_cargo_date(self):
        if not hasattr(self, '_cargo_date'):
            self.parse_nightly_dates()
        return self._cargo_date

    def snap_rustc_date(self):
        if not hasattr(self, '_rustc_date'):
            self.parse_nightly_dates()
        return self._rustc_date

    def cargo_root(self):
        return os.path.join(self.build_dir, self.build, "snapshot-cargo",
                            self.snap_cargo_date())

    def rustc_root(self):
        return os.path.join(self.build_dir, self.build, "snapshot-rustc",
                            self.snap_rustc_date())

    def cargo(self):
        return os.path.join(self.cargo_root(),
                            "cargo/bin/cargo" + self.exe_suffix())

    def rustc(self):
        return os.path.join(self.rustc_root(),
                            "rustc/bin/rustc" + self.exe_suffix())

    def exe_suffix(self):
        if sys.platform == 'win32':
            return '.exe'
        else:
            return ''

    def parse_nightly_dates(self):
        nightlies = os.path.join(self.rust_root, "src/nightlies.txt")
        rustc, cargo = open(nightlies, 'r').read().split("\n")[:2]
        assert(rustc.startswith("rustc: "))
        assert(cargo.startswith("cargo: "))
        self._rustc_date = rustc[len("rustc: "):]
        self._cargo_date = cargo[len("cargo: "):]

    def build_bootstrap(self):
        env = os.environ.copy()
        env["CARGO_TARGET_DIR"] = os.path.join(self.build_dir, "bootstrap")
        env["RUSTC"] = self.rustc()
        env["LD_LIBRARY_PATH"] = os.path.join(self.rustc_root(), "rustc/lib")
        env["DYLD_LIBRARY_PATH"] = os.path.join(self.rustc_root(), "rustc/lib")
        env["PATH"] = os.path.join(self.rustc_root(), "rustc/bin") + \
                      os.pathsep + env["PATH"]

        self.run([self.cargo(), "build", "--manifest-path",
                  os.path.join(self.rust_root, "src/bootstrap/Cargo.toml")],
                 env)

    def run(self, args, env):
        ret = subprocess.Popen(args, env = env).wait()
        if ret != 0:
            exit(ret)

def build_triple():
    try:
        ostype = subprocess.check_output(['uname', '-s']).strip()
        cputype = subprocess.check_output(['uname', '-m']).strip()
    except FileNotFoundError:
        if sys.platform == 'win32':
            return 'x86_64-pc-windows-msvc'
        else:
            raise

    # Darwin's `uname -s` lies and always returns i386. We have to use sysctl
    # instead.
    if ostype == 'Darwin' and cputype == 'i686':
        sysctl = subprocess.check_output(['sysctl', 'hw.optional.x86_64'])
        if sysctl.contains(': 1'):
            cputype = 'x86_64'

    # The goal here is to come up with the same triple as LLVM would,
    # at least for the subset of platforms we're willing to target.
    if ostype == 'Linux':
        ostype = 'unknown-linux-gnu'
    elif ostype == 'FreeBSD':
        ostype = 'unknown-freebsd'
    elif ostype == 'DragonFly':
        ostype = 'unknown-dragonfly'
    elif ostype == 'Bitrig':
        ostype = 'unknown-bitrig'
    elif ostype == 'OpenBSD':
        ostype = 'unknown-openbsd'
    elif ostype == 'NetBSD':
        ostype = 'unknown-netbsd'
    elif ostype == 'Darwin':
        ostype = 'apple-darwin'
    elif ostype.startswith('MINGW'):
        # msys' `uname` does not print gcc configuration, but prints msys
        # configuration. so we cannot believe `uname -m`:
        # msys1 is always i686 and msys2 is always x86_64.
        # instead, msys defines $MSYSTEM which is MINGW32 on i686 and
        # MINGW64 on x86_64.
        ostype = 'pc-windows-gnu'
        cputype = 'i686'
        if os.environ.get('MSYSTEM') == 'MINGW64':
            cputype = 'x86_64'
    elif ostype.startswith('MSYS'):
        ostype = 'pc-windows-gnu'
    elif ostype.startswith('CYGWIN_NT'):
        cputype = 'i686'
        if ostype.endswith('WOW64'):
            cputype = 'x86_64'
        ostype = 'pc-windows-gnu'
    else:
        raise Exception("unknown OS type: " + ostype)

    if (cputype == 'i386' or cputype == 'i486' or cputype == 'i686' or
            cputype == 'i786' or cputype == 'x86'):
        cputype = 'i686'
    elif cputype == 'xscale' or cputype == 'arm':
        cputype = 'arm'
    elif cputype == 'armv7l':
        cputype = 'arm'
        ostype += 'eabihf'
    elif cputype == 'aarch64':
        cputype = 'aarch64'
    elif cputype == 'powerpc' or cputype == 'ppc' or cputype == 'ppc64':
        cputype = 'powerpc'
    elif (cputype == 'amd64' or cputype == 'x86_64' or cputype == 'x86-64' or
            cputype =='x64'):
        cputype = 'x86_64'
    else:
        raise Exception("unknown cpu type: " + cputype)

    return cputype + '-' + ostype

# Configure initial bootstrap
rb = RustBuild()
rb.rust_root = os.path.dirname(os.path.abspath(__file__))
rb.rust_root = os.path.dirname(os.path.dirname(os.path.dirname(rb.rust_root)))
rb.build_dir = os.path.join(os.getcwd(), "target")
rb.build = build_triple();

# Fetch/build the bootstrap
rb.download_rust_nightly()
sys.stdout.flush()
rb.build_bootstrap()
sys.stdout.flush()

# Run the bootstrap
args = [os.path.join(rb.build_dir, "bootstrap/debug/bootstrap")]
args.extend(sys.argv[1:])
env = os.environ.copy()
env["RUSTC"] = rb.rustc()
env["CARGO"] = rb.cargo()
env["BUILD_DIR"] = rb.build_dir
env["SRC_DIR"] = rb.rust_root
env["BUILD"] = rb.build
rb.run(args, env)
