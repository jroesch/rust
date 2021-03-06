// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::prelude::*;

use libc::types::os::arch::extra::{LPVOID, DWORD, LONG};
use libc;
use mem;
use ptr;
use rt::util::report_overflow;
use sys::c;
use sys_common::stack;

pub struct Handler {
    _data: *mut libc::c_void
}

impl Handler {
    pub unsafe fn new() -> Handler {
        make_handler()
    }
}

impl Drop for Handler {
    fn drop(&mut self) {}
}

// This is initialized in init() and only read from after
static mut PAGE_SIZE: usize = 0;

#[no_stack_check]
extern "system" fn vectored_handler(ExceptionInfo: *mut EXCEPTION_POINTERS) -> LONG {
    unsafe {
        let rec = &(*(*ExceptionInfo).ExceptionRecord);
        let code = rec.ExceptionCode;

        if code != EXCEPTION_STACK_OVERFLOW {
            return EXCEPTION_CONTINUE_SEARCH;
        }

        // We're calling into functions with stack checks,
        // however stack checks by limit should be disabled on Windows
        stack::record_sp_limit(0);

        report_overflow();

        EXCEPTION_CONTINUE_SEARCH
    }
}

pub unsafe fn init() {
    let mut info = mem::zeroed();
    libc::GetSystemInfo(&mut info);
    PAGE_SIZE = info.dwPageSize as usize;

    if AddVectoredExceptionHandler(0, vectored_handler) == ptr::null_mut() {
        panic!("failed to install exception handler");
    }

    mem::forget(make_handler());
}

pub unsafe fn cleanup() {
}

pub unsafe fn make_handler() -> Handler {
    // This API isn't available on XP, so don't panic in that case and just pray
    // it works out ok.
    if c::SetThreadStackGuarantee(&mut 0x5000) == 0 {
        if libc::GetLastError() as u32 != libc::ERROR_CALL_NOT_IMPLEMENTED as u32 {
            panic!("failed to reserve stack space for exception handling");
        }
    }

    Handler { _data: 0 as *mut libc::c_void }
}

#[repr(C)]
pub struct EXCEPTION_RECORD {
    pub ExceptionCode: DWORD,
    pub ExceptionFlags: DWORD,
    pub ExceptionRecord: *mut EXCEPTION_RECORD,
    pub ExceptionAddress: LPVOID,
    pub NumberParameters: DWORD,
    pub ExceptionInformation: [LPVOID; EXCEPTION_MAXIMUM_PARAMETERS]
}

#[repr(C)]
pub struct EXCEPTION_POINTERS {
    pub ExceptionRecord: *mut EXCEPTION_RECORD,
    pub ContextRecord: LPVOID
}

pub type PVECTORED_EXCEPTION_HANDLER = extern "system"
        fn(ExceptionInfo: *mut EXCEPTION_POINTERS) -> LONG;

pub type ULONG = libc::c_ulong;

const EXCEPTION_CONTINUE_SEARCH: LONG = 0;
const EXCEPTION_MAXIMUM_PARAMETERS: usize = 15;
const EXCEPTION_STACK_OVERFLOW: DWORD = 0xc00000fd;

extern "system" {
    fn AddVectoredExceptionHandler(FirstHandler: ULONG,
                                   VectoredHandler: PVECTORED_EXCEPTION_HANDLER)
                                  -> LPVOID;
}
