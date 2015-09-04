// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::infer::InferCtxt;
use middle::traits::{self, Normalized, MiscObligation,
                     SelectionContext, ObligationCause};
use middle::ty::HasTypeFlags;
use middle::ty::fold::TypeFoldable;
use syntax::ast;
use syntax::codemap::Span;

pub fn normalize_associated_types_in<'a,'tcx,T>(infcx: &mut InferCtxt<'a,'tcx>,
                                                span: Span,
                                                body_id: ast::NodeId,
                                                value: &T)
                                                -> T
    where T : TypeFoldable<'tcx> + HasTypeFlags
{
    debug!("normalize_associated_types_in(value={:?})", value);
    SelectionContext::scoped(infcx, |mut selcx| {
        let cause = ObligationCause::new(span, body_id, MiscObligation);
        let Normalized { value: result, obligations } = traits::normalize(&mut selcx, cause, value);
        debug!("normalize_associated_types_in: result={:?} predicates={:?}",
               result,
               obligations);
        for obligation in obligations {
            selcx.infcx().register_predicate_obligation(obligation);
        }
        result
     })
}
