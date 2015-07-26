// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::combine::{self, CombineFields};
use super::InferCtxt;
use super::higher_ranked::HigherRankedRelations;
use super::{Subtype};
use super::type_variable::{EqTo};

use middle::ty::{self, Ty};
use middle::ty::TyVar;
use middle::ty::relate::{Relate, RelateResult, TypeRelation};

use std::cell::{RefMut};

pub struct Equate<'infcx, 'a: 'infcx, 'tcx: 'a> {
    fields: CombineFields<'infcx, 'a, 'tcx>
}

impl< 'infcx, 'a, 'tcx> Equate< 'infcx, 'a, 'tcx> {
    pub fn new(fields: CombineFields<'infcx, 'a, 'tcx>) -> Equate< 'infcx, 'a, 'tcx> {
        Equate { fields: fields }
    }
}

impl<'infcx, 'a, 'tcx> TypeRelation<'infcx,'a,'tcx> for Equate<'infcx, 'a, 'tcx> {
    fn tag(&self) -> &'static str { "Equate" }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> { self.fields.tcx() }

    fn infcx(&self) -> RefMut<&'infcx mut InferCtxt<'a, 'tcx>> {
         self.fields.infcx.borrow_mut()
    }

    fn a_is_expected(&self) -> bool { self.fields.a_is_expected }

    fn relate_with_variance<T:Relate<'a,'tcx>>(&mut self,
                                               _: ty::Variance,
                                               a: &T,
                                               b: &T)
                                               -> RelateResult<'tcx, T>
    {
        self.relate(a, b)
    }

    fn tys(&mut self, a: Ty<'tcx>, b: Ty<'tcx>) -> RelateResult<'tcx, Ty<'tcx>> {
        debug!("{}.tys({:?}, {:?})", self.tag(),
               a, b);
        if a == b { return Ok(a); }

        let (a, b) = {
            let infcx = self.fields.infcx.borrow_mut();
            let a = infcx.type_variables.borrow().replace_if_possible(a);
            let b = infcx.type_variables.borrow().replace_if_possible(b);
            (a, b)
        };

        match (&a.sty, &b.sty) {
            (&ty::TyInfer(TyVar(a_id)), &ty::TyInfer(TyVar(b_id))) => {
                let infcx = self.fields.infcx.borrow_mut();
                infcx.type_variables.borrow_mut().relate_vars(a_id, EqTo, b_id);
                Ok(a)
            }

            (&ty::TyInfer(TyVar(a_id)), _) => {
                try!(self.fields.instantiate(b, EqTo, a_id));
                Ok(a)
            }

            (_, &ty::TyInfer(TyVar(b_id))) => {
                try!(self.fields.instantiate(a, EqTo, b_id));
                Ok(a)
            }

            _ => {
                try!(combine::super_combine_tys(self.fields.infcx, self, a, b));
                Ok(a)
            }
        }
    }

    fn regions(&mut self, a: ty::Region, b: ty::Region) -> RelateResult<'tcx, ty::Region> {
        debug!("{}.regions({:?}, {:?})",
               self.tag(),
               a,
               b);
        let origin = Subtype(self.fields.trace.clone());
        self.fields.infcx.borrow_mut().region_vars.make_eqregion(origin, a, b);
        Ok(a)
    }

    fn binders<T>(&mut self, a: &ty::Binder<T>, b: &ty::Binder<T>)
                  -> RelateResult<'tcx, ty::Binder<T>>
        where T: Relate<'a, 'tcx>
    {
        try!(self.fields.higher_ranked_sub(a, b));
        self.fields.higher_ranked_sub(b, a)
    }
}
