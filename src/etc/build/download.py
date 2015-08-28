# Copyright 2015 The Rust Project Developers. See the COPYRIGHT
# file at the top-level directory of this distribution and at
# http://rust-lang.org/COPYRIGHT.
#
# Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
# http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
# <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
# option. This file may not be copied, modified, or distributed
# except according to those terms.

import contextlib
import os
import shutil
import subprocess
import sys
import tarfile

def get(url, path, quiet=False):
    # see http://serverfault.com/questions/301128/how-to-download
    if sys.platform == 'win32':
        run(["PowerShell.exe", "/nologo", "-Command",
             "(New-Object System.Net.WebClient).DownloadFile('" + url +
                "', '" + path + "')"], quiet=quiet)
    else:
        run(["curl", "-o", path, url], quiet=quiet)

def unpack(tarball, dst, quiet=False):
    if quiet:
        print("extracting " + tarball)
    fname = os.path.basename(tarball).replace(".tar.gz", "")
    with contextlib.closing(tarfile.open(tarball)) as tar:
        for p in tar.getnames():
            name = p.replace(fname + "/", "", 1)
            fp = os.path.join(dst, name)
            if not quiet:
                print("extracting " + p)
            tar.extract(p, dst)
            tp = os.path.join(dst, p)
            if os.path.isdir(tp) and os.path.exists(fp):
                continue
            shutil.move(tp, fp)
    shutil.rmtree(os.path.join(dst, fname))

def run(args, quiet=False):
    if not quiet:
        print("running: " + ' '.join(args))
    sys.stdout.flush()
    # Use Popen here instead of call() as it apparently allows powershell on
    # Windows to not lock up waiting for input presumably.
    ret = subprocess.Popen(args,
                           stdin = subprocess.PIPE,
                           stdout = subprocess.PIPE,
                           stderr = subprocess.PIPE)
    out, err = ret.communicate()
    code = ret.wait()
    if code != 0:
        print("stdout: \n\n" + out)
        print("stderr: \n\n" + err)
        raise Exception("failed to fetch url")
