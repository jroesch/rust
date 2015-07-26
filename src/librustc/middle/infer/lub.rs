// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::combine::CombineFields;
use super::higher_ranked::HigherRankedRelations;
use super::InferCtxt;
use super::lattice::{self, LatticeDir};
use super::Subtype;

use middle::ty::{self, Ty};
use middle::ty::relate::{Relate, RelateResult, TypeRelation};

use std::cell::{RefMut};

/// "Least upper bound" (common supertype)
pub struct Lub<'infcx, 'a: 'infcx, 'tcx: 'a> {
    fields: CombineFields<'infcx, 'a, 'tcx>
}

impl<'infcx, 'a, 'tcx> Lub<'infcx, 'a, 'tcx> {
    pub fn new(fields: CombineFields<'infcx, 'a, 'tcx>) -> Lub<'infcx, 'a, 'tcx> {
        Lub { fields: fields }
    }
}

impl<'infcx, 'a, 'tcx> TypeRelation<'infcx, 'a, 'tcx> for Lub<'infcx, 'a, 'tcx> {
    fn tag(&self) -> &'static str { "Lub" }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> { self.fields.tcx() }

    fn infcx(&self) -> RefMut<&'infcx mut InferCtxt<'a, 'tcx>> {
        self.fields.infcx.borrow_mut()
    }

    fn a_is_expected(&self) -> bool { self.fields.a_is_expected }

    fn relate_with_variance<T:Relate<'a,'tcx>>(&mut self,
                                                      variance: ty::Variance,
                                                      a: &T,
                                                      b: &T)
                                                      -> RelateResult<'tcx, T>
    {
        match variance {
            ty::Invariant => self.fields.equate().relate(a, b),
            ty::Covariant => self.relate(a, b),
            ty::Bivariant => self.fields.bivariate().relate(a, b),
            ty::Contravariant => self.fields.glb().relate(a, b),
        }
    }

    fn tys(&mut self, a: Ty<'tcx>, b: Ty<'tcx>) -> RelateResult<'tcx, Ty<'tcx>> {
        lattice::super_lattice_tys(self, a, b)
    }

    fn regions(&mut self, a: ty::Region, b: ty::Region) -> RelateResult<'tcx, ty::Region> {
        debug!("{}.regions({:?}, {:?})",
               self.tag(),
               a,
               b);

        let origin = Subtype(self.fields.trace.clone());
        Ok(self.fields.infcx.borrow().region_vars.lub_regions(origin, a, b))
    }

    fn binders<T>(&mut self, a: &ty::Binder<T>, b: &ty::Binder<T>)
                  -> RelateResult<'tcx, ty::Binder<T>>
        where T: Relate<'a, 'tcx>
    {
        self.fields.higher_ranked_lub(a, b)
    }
}

impl<'infcx, 'a, 'tcx> LatticeDir<'infcx,'a,'tcx> for Lub<'infcx, 'a, 'tcx> {
    fn relate_bound(&self, v: Ty<'tcx>, a: Ty<'tcx>, b: Ty<'tcx>) -> RelateResult<'tcx, ()> {
        let mut sub = self.fields.sub();
        try!(sub.relate(&a, &v));
        try!(sub.relate(&b, &v));
        Ok(())
    }
}
