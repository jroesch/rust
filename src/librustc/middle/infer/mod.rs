// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! See the Book for more information.

pub use self::LateBoundRegionConversionTime::*;
pub use self::RegionVariableOrigin::*;
pub use self::SubregionOrigin::*;
pub use self::ValuePairs::*;
pub use middle::ty::IntVarValue;
pub use self::freshen::TypeFreshener;
pub use self::region_inference::{GenericKind, VerifyBound};

use middle::def_id::DefId;
use rustc_front::hir;
use middle::free_region::FreeRegionMap;
use middle::mem_categorization as mc;
use middle::mem_categorization::McResult;
use middle::region::CodeExtent;
use middle::subst;
use middle::subst::Substs;
use middle::subst::Subst;
use middle::traits::{self, CodeAmbiguity, CodeSelectionError, CodeProjectionError,
                     Normalized, SelectionContext, ObligationCause,
                     ObligationCauseCode, PredicateObligation,
                     Unimplemented, FulfillmentError, RFC1214Warning, TraitErrorKey};
use middle::ty::adjustment;
use middle::traits::project;
use middle::traits::is_object_safe;
use middle::traits::util::{predicate_for_builtin_bound};
use middle::transactional::TransactionalMut;
use middle::ty::{TyVid, IntVid, FloatVid, RegionVid};
use middle::ty::{self, Ty, HasTypeFlags, RegionEscape};
use middle::ty::error::{ExpectedFound, TypeError, UnconstrainedNumeric};
use middle::ty::fold::{TypeFolder, TypeFoldable};
use middle::ty::relate::{Relate, RelateResult, TypeRelation};

use rustc_data_structures::snapshot_vec::{Snapshot, SnapshotVec, SnapshotVecDelegate};
use rustc_data_structures::snapshot_tree::{SnapshotTree};
use rustc_data_structures::unify::{self, UnificationTable};
use std::cell::{RefCell, Ref};
use std::fmt;
use std::rc::Rc;
use std::mem;
use syntax::ast;
use syntax::codemap;
use syntax::codemap::{Span, DUMMY_SP};
use syntax::errors::DiagnosticBuilder;
use util::nodemap::{FnvHashMap, FnvHashSet, NodeMap};
use util::common::ErrorReported;

use self::combine::CombineFields;
use self::region_inference::{RegionVarBindings, RegionSnapshot};
use self::error_reporting::ErrorReporting;
use self::unify_key::ToType;

pub mod bivariate;
pub mod combine;
pub mod equate;
pub mod error_reporting;
pub mod glb;
mod higher_ranked;
pub mod lattice;
pub mod lub;
pub mod region_inference;
pub mod resolve;
mod freshen;
pub mod sub;
pub mod type_variable;
pub mod unify_key;

pub type Bound<T> = Option<T>;
pub type UnitResult<'tcx> = RelateResult<'tcx, ()>; // "unify result"
pub type FixupResult<T> = Result<T, FixupError>; // "fixup result"

pub struct InferCtxt<'a, 'tcx: 'a> {
    pub tcx: &'a ty::ctxt<'tcx>,

    pub tables: &'a RefCell<ty::Tables<'tcx>>,

    // We instantiate UnificationTable with bounds<Ty> because the
    // types that might instantiate a general type variable have an
    // order, represented by its upper and lower bounds.
    pub type_variables: RefCell<type_variable::TypeVariableTable<'tcx>>,

    // Map from integral variable to the kind of integer it represents
    pub int_unification_table: RefCell<UnificationTable<ty::IntVid>>,

    // Map from floating variable to the kind of float it represents
    pub float_unification_table: RefCell<UnificationTable<ty::FloatVid>>,

    // For region variables.
    pub region_vars: RegionVarBindings<'a, 'tcx>,

    pub parameter_environment: ty::ParameterEnvironment<'a, 'tcx>,

    // This is a temporary field used for toggling on normalization in the inference context,
    // as we move towards the approach described here:
    // https://internals.rust-lang.org/t/flattening-the-contexts-for-fun-and-profit/2293
    // At a point sometime in the future normalization will be done by the typing context
    // directly.
    normalize: bool,

    err_count_on_creation: usize,

    pub reported_trait_errors: RefCell<FnvHashSet<TraitErrorKey<'tcx>>>,

    /// The fulfillment context is used to drive trait resolution.  It
    /// consists of a list of obligations that must be (eventually)
    /// satisfied. The job is to track which are satisfied, which yielded
    /// errors, and which are still pending. At any point, users can call
    /// `select_where_possible`, and the fulfilment context will try to do
    /// selection, retaining only those obligations that remain
    /// ambiguous. This may be helpful in pushing type inference
    /// along. Once all type inference constraints have been generated, the
    /// method `select_all_or_error` can be used to report any remaining
    /// ambiguous cases as errors.

    // a simple cache that aims to cache *exact duplicate obligations*
    // and avoid adding them twice. This serves a different purpose
    // than the `SelectionCache`: it avoids duplicate errors and
    // permits recursive obligations, which are often generated from
    // traits like `Send` et al.
    pub duplicate_set: FulfilledPredicates<'tcx>,

    // A list of all obligations that have been registered with this
    // fulfillment context.
    pub predicates: SnapshotTree<PendingPredicateObligation<'tcx>>,

    // Remembers the count of trait obligations that we have already
    // attempted to select. This is used to avoid repeating work
    // when `select_new_obligations` is called.
    pub attempted_mark: usize,

    // A set of constraints that regionck must validate. Each
    // constraint has the form `T:'a`, meaning "some type `T` must
    // outlive the lifetime 'a". These constraints derive from
    // instantiated type parameters. So if you had a struct defined
    // like
    //
    //     struct Foo<T:'static> { ... }
    //
    // then in some expression `let x = Foo { ... }` it will
    // instantiate the type parameter `T` with a fresh type `$0`. At
    // the same time, it will record a region obligation of
    // `$0:'static`. This will get checked later by regionck. (We
    // can't generally check these things right away because we have
    // to wait until types are resolved.)
    //
    // These are stored in a map keyed to the id of the innermost
    // enclosing fn body / static initializer expression. This is
    // because the location where the obligation was incurred can be
    // relevant with respect to which sublifetime assumptions are in
    // place. The reason that we store under the fn-id, and not
    // something more fine-grained, is so that it is easier for
    // regionck to be sure that it has found *all* the region
    // obligations (otherwise, it's easy to fail to walk to a
    // particular node-id).
    pub region_obligations: NodeMap<SnapshotVec<RegionObligation<'tcx>>>,

    pub errors_will_be_reported: bool,
}

pub trait HasInferCtxt<'a, 'tcx> {
    fn infer_ctxt(&self) -> &mut InferCtxt<'a, 'tcx>;
}

/// A map returned by `skolemize_late_bound_regions()` indicating the skolemized
/// region that each late-bound region was replaced with.
pub type SkolemizationMap = FnvHashMap<ty::BoundRegion,ty::Region>;

/// Why did we require that the two types be related?
///
/// See `error_reporting.rs` for more details
#[derive(Clone, Copy, Debug)]
pub enum TypeOrigin {
    // Not yet categorized in a better way
    Misc(Span),

    // Checking that method of impl is compatible with trait
    MethodCompatCheck(Span),

    // Checking that this expression can be assigned where it needs to be
    // FIXME(eddyb) #11161 is the original Expr required?
    ExprAssignable(Span),

    // Relating trait refs when resolving vtables
    RelateTraitRefs(Span),

    // Relating self types when resolving vtables
    RelateSelfType(Span),

    // Relating trait type parameters to those found in impl etc
    RelateOutputImplTypes(Span),

    // Computing common supertype in the arms of a match expression
    MatchExpressionArm(Span, Span, hir::MatchSource),

    // Computing common supertype in an if expression
    IfExpression(Span),

    // Computing common supertype of an if expression with no else counter-part
    IfExpressionWithNoElse(Span),

    // Computing common supertype in a range expression
    RangeExpression(Span),

    // `where a == b`
    EquatePredicate(Span),
}

impl TypeOrigin {
    fn as_str(&self) -> &'static str {
        match self {
            &TypeOrigin::Misc(_) |
            &TypeOrigin::RelateSelfType(_) |
            &TypeOrigin::RelateOutputImplTypes(_) |
            &TypeOrigin::ExprAssignable(_) => "mismatched types",
            &TypeOrigin::RelateTraitRefs(_) => "mismatched traits",
            &TypeOrigin::MethodCompatCheck(_) => "method not compatible with trait",
            &TypeOrigin::MatchExpressionArm(_, _, source) => match source {
                hir::MatchSource::IfLetDesugar{..} => "`if let` arms have incompatible types",
                _ => "match arms have incompatible types",
            },
            &TypeOrigin::IfExpression(_) => "if and else have incompatible types",
            &TypeOrigin::IfExpressionWithNoElse(_) => "if may be missing an else clause",
            &TypeOrigin::RangeExpression(_) => "start and end of range have incompatible types",
            &TypeOrigin::EquatePredicate(_) => "equality predicate not satisfied",
        }
    }
}

impl fmt::Display for TypeOrigin {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(),fmt::Error> {
        fmt::Display::fmt(self.as_str(), f)
    }
}

/// See `error_reporting.rs` for more details
#[derive(Clone, Debug)]
pub enum ValuePairs<'tcx> {
    Types(ExpectedFound<Ty<'tcx>>),
    TraitRefs(ExpectedFound<ty::TraitRef<'tcx>>),
    PolyTraitRefs(ExpectedFound<ty::PolyTraitRef<'tcx>>),
}

/// The trace designates the path through inference that we took to
/// encounter an error or subtyping constraint.
///
/// See `error_reporting.rs` for more details.
#[derive(Clone)]
pub struct TypeTrace<'tcx> {
    origin: TypeOrigin,
    values: ValuePairs<'tcx>,
}

/// The origin of a `r1 <= r2` constraint.
///
/// See `error_reporting.rs` for more details
#[derive(Clone, Debug)]
pub enum SubregionOrigin<'tcx> {
    // Arose from a subtyping relation
    Subtype(TypeTrace<'tcx>),

    // Stack-allocated closures cannot outlive innermost loop
    // or function so as to ensure we only require finite stack
    InfStackClosure(Span),

    // Invocation of closure must be within its lifetime
    InvokeClosure(Span),

    // Dereference of reference must be within its lifetime
    DerefPointer(Span),

    // Closure bound must not outlive captured free variables
    FreeVariable(Span, ast::NodeId),

    // Index into slice must be within its lifetime
    IndexSlice(Span),

    // When casting `&'a T` to an `&'b Trait` object,
    // relating `'a` to `'b`
    RelateObjectBound(Span),

    // Some type parameter was instantiated with the given type,
    // and that type must outlive some region.
    RelateParamBound(Span, Ty<'tcx>),

    // The given region parameter was instantiated with a region
    // that must outlive some other region.
    RelateRegionParamBound(Span),

    // A bound placed on type parameters that states that must outlive
    // the moment of their instantiation.
    RelateDefaultParamBound(Span, Ty<'tcx>),

    // Creating a pointer `b` to contents of another reference
    Reborrow(Span),

    // Creating a pointer `b` to contents of an upvar
    ReborrowUpvar(Span, ty::UpvarId),

    // Data with type `Ty<'tcx>` was borrowed
    DataBorrowed(Ty<'tcx>, Span),

    // (&'a &'b T) where a >= b
    ReferenceOutlivesReferent(Ty<'tcx>, Span),

    // Type or region parameters must be in scope.
    ParameterInScope(ParameterOrigin, Span),

    // The type T of an expression E must outlive the lifetime for E.
    ExprTypeIsNotInScope(Ty<'tcx>, Span),

    // A `ref b` whose region does not enclose the decl site
    BindingTypeIsNotValidAtDecl(Span),

    // Regions appearing in a method receiver must outlive method call
    CallRcvr(Span),

    // Regions appearing in a function argument must outlive func call
    CallArg(Span),

    // Region in return type of invoked fn must enclose call
    CallReturn(Span),

    // Operands must be in scope
    Operand(Span),

    // Region resulting from a `&` expr must enclose the `&` expr
    AddrOf(Span),

    // An auto-borrow that does not enclose the expr where it occurs
    AutoBorrow(Span),

    // Region constraint arriving from destructor safety
    SafeDestructor(Span),
}

/// Places that type/region parameters can appear.
#[derive(Clone, Copy, Debug)]
pub enum ParameterOrigin {
    Path, // foo::bar
    MethodCall, // foo.bar() <-- parameters on impl providing bar()
    OverloadedOperator, // a + b when overloaded
    OverloadedDeref, // *a when overloaded
}

/// Times when we replace late-bound regions with variables:
#[derive(Clone, Copy, Debug)]
pub enum LateBoundRegionConversionTime {
    /// when a fn is called
    FnCall,

    /// when two higher-ranked types are compared
    HigherRankedType,

    /// when projecting an associated type
    AssocTypeProjection(ast::Name),
}

/// Reasons to create a region inference variable
///
/// See `error_reporting.rs` for more details
#[derive(Clone, Debug)]
pub enum RegionVariableOrigin {
    // Region variables created for ill-categorized reasons,
    // mostly indicates places in need of refactoring
    MiscVariable(Span),

    // Regions created by a `&P` or `[...]` pattern
    PatternRegion(Span),

    // Regions created by `&` operator
    AddrOfRegion(Span),

    // Regions created as part of an autoref of a method receiver
    Autoref(Span),

    // Regions created as part of an automatic coercion
    Coercion(Span),

    // Region variables created as the values for early-bound regions
    EarlyBoundRegion(Span, ast::Name),

    // Region variables created for bound regions
    // in a function or method that is called
    LateBoundRegion(Span, ty::BoundRegion, LateBoundRegionConversionTime),

    UpvarRegion(ty::UpvarId, Span),

    BoundRegionInCoherence(ast::Name),
}

#[derive(Copy, Clone, Debug)]
pub enum FixupError {
    UnresolvedIntTy(IntVid),
    UnresolvedFloatTy(FloatVid),
    UnresolvedTy(TyVid)
}

pub fn fixup_err_to_string(f: FixupError) -> String {
    use self::FixupError::*;

    match f {
      UnresolvedIntTy(_) => {
          "cannot determine the type of this integer; add a suffix to \
           specify the type explicitly".to_string()
      }
      UnresolvedFloatTy(_) => {
          "cannot determine the type of this number; add a suffix to specify \
           the type explicitly".to_string()
      }
      UnresolvedTy(_) => "unconstrained type".to_string(),
    }
}

pub fn mk_subty<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>,
                          a_is_expected: bool,
                          origin: TypeOrigin,
                          a: Ty<'tcx>,
                          b: Ty<'tcx>)
                          -> UnitResult<'tcx>
{
    debug!("mk_subty({:?} <: {:?})", a, b);
    cx.sub_types(a_is_expected, origin, a, b)
}

pub fn can_mk_subty<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>,
                              a: Ty<'tcx>,
                              b: Ty<'tcx>)
                              -> UnitResult<'tcx> {
    debug!("can_mk_subty({:?} <: {:?})", a, b);
    cx.probe(|_, _| {
        let trace = TypeTrace {
            origin: TypeOrigin::Misc(codemap::DUMMY_SP),
            values: Types(expected_found(true, a, b))
        };
        cx.sub(true, trace).relate(&a, &b).map(|_| ())
    })
}

pub fn can_mk_eqty<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>, a: Ty<'tcx>, b: Ty<'tcx>)
                             -> UnitResult<'tcx>
{
    cx.can_equate(&a, &b)
}

pub fn mk_subr<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>,
                         origin: SubregionOrigin<'tcx>,
                         a: ty::Region,
                         b: ty::Region) {
    debug!("mk_subr({:?} <: {:?})", a, b);
    let snapshot = cx.region_vars.start_snapshot();
    cx.region_vars.make_subregion(origin, a, b);
    cx.region_vars.commit(snapshot);
}

pub fn mk_eqty<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>,
                         a_is_expected: bool,
                         origin: TypeOrigin,
                         a: Ty<'tcx>,
                         b: Ty<'tcx>)
                         -> UnitResult<'tcx>
{
    debug!("mk_eqty({:?} <: {:?})", a, b);
    cx.commit_if_ok(|_| cx.eq_types(a_is_expected, origin, a, b))
}

pub fn mk_eq_trait_refs<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>,
                                   a_is_expected: bool,
                                   origin: TypeOrigin,
                                   a: ty::TraitRef<'tcx>,
                                   b: ty::TraitRef<'tcx>)
                                   -> UnitResult<'tcx>
{
    debug!("mk_eq_trait_refs({:?} <: {:?})",
           a, b);
    cx.commit_if_ok(|_, _| cx.eq_trait_refs(a_is_expected, origin, a.clone(), b.clone()))
}

pub fn mk_sub_poly_trait_refs<'a, 'tcx>(cx: &InferCtxt<'a, 'tcx>,
                                        a_is_expected: bool,
                                        origin: TypeOrigin,
                                        a: ty::PolyTraitRef<'tcx>,
                                        b: ty::PolyTraitRef<'tcx>)
                                        -> UnitResult<'tcx>
{
    debug!("mk_sub_poly_trait_refs({:?} <: {:?})",
           a, b);
    cx.commit_if_ok(|_| cx.sub_poly_trait_refs(a_is_expected, origin, a.clone(), b.clone()))
}

fn expected_found<T>(a_is_expected: bool,
                     a: T,
                     b: T)
                     -> ExpectedFound<T>
{
    if a_is_expected {
        ExpectedFound {expected: a, found: b}
    } else {
        ExpectedFound {expected: b, found: a}
    }
}

#[must_use = "once you start a snapshot, you should always consume it"]
pub struct CombinedSnapshot<'tcx> {
    pub type_snapshot: type_variable::Snapshot,
    pub int_snapshot: unify::Snapshot<ty::IntVid>,
    pub float_snapshot: unify::Snapshot<ty::FloatVid>,
    pub region_vars_snapshot: RegionSnapshot,
    pub predicates_snapshot: Snapshot,
    pub region_obligations_snapshot: NodeMap<Snapshot>,
    pub duplicate_set: FulfilledPredicates<'tcx>,
}

pub fn normalize_associated_type<'tcx,T>(tcx: &ty::ctxt<'tcx>, value: &T) -> T
    where T : TypeFoldable<'tcx> + HasTypeFlags
{
    debug!("normalize_associated_type(t={:?})", value);

    let value = tcx.erase_regions(value);

    if !value.has_projection_types() {
        return value;
    }

    let mut infcx = InferCtxt::new(tcx, &tcx.tables, None, true);

    let traits::Normalized { value: result, obligations } = {
        let cell = RefCell::new(&mut infcx);
        let mut selcx = traits::SelectionContext::new(&cell);
        let cause = traits::ObligationCause::dummy();
        traits::normalize(&mut selcx, cause, &value)
    };

    debug!("normalize_associated_type: result={:?} obligations={:?}",
           result,
           obligations);


    for obligation in obligations {
        infcx.register_predicate_obligation(obligation);
    }

    let result = infcx.drain_fulfillment_cx_or_panic(&result, DUMMY_SP);

    result
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    /// errors_will_be_reported is required to proxy to the fulfillment context
    /// FIXME -- a better option would be to hold back on modifying
    /// the global cache until we know that all dependent obligations
    /// are also satisfied. In that case, we could actually remove
    /// this boolean flag, and we'd also avoid the problem of squelching
    /// duplicate errors that occur across fns.
    pub fn new(tcx: &'a ty::ctxt<'tcx>,
               tables: &'a RefCell<ty::Tables<'tcx>>,
               param_env: Option<ty::ParameterEnvironment<'a, 'tcx>>,
               errors_will_be_reported: bool)
               -> InferCtxt<'a, 'tcx> {
        InferCtxt {
            tcx: tcx,
            tables: tables,
            type_variables: RefCell::new(type_variable::TypeVariableTable::new()),
            int_unification_table: RefCell::new(UnificationTable::new()),
            float_unification_table: RefCell::new(UnificationTable::new()),
            region_vars: RegionVarBindings::new(tcx),
            parameter_environment: param_env.unwrap_or(tcx.empty_parameter_environment()),
            normalize: false,
            err_count_on_creation: tcx.sess.err_count(),
            // `errors_will_be_reported` indicates whether ALL errors that
            // are generated by this fulfillment context will be reported to
            // the end user. This is used to inform caching, because it
            // allows us to conclude that traits that resolve successfully
            // will in fact always resolve successfully (in particular, it
            // guarantees that if some dependent obligation encounters a
            // problem, compilation will be aborted).  If you're not sure of
            // the right value here, pass `false`, as that is the more
            // conservative option.
            //
            // FIXME -- a better option would be to hold back on modifying
            // the global cache until we know that all dependent obligations
            // are also satisfied. In that case, we could actually remove
            // this boolean flag, and we'd also avoid the problem of squelching
            // duplicate errors that occur across fns.
            duplicate_set: FulfilledPredicates::new(),
            predicates: SnapshotTree::new(),
            attempted_mark: 0,
            region_obligations: NodeMap(),
            errors_will_be_reported: errors_will_be_reported,
            reported_trait_errors: RefCell::new(FnvHashSet()),
        }
    }

    pub fn normalizing(tcx: &'a ty::ctxt<'tcx>,
                       tables: &'a RefCell<ty::Tables<'tcx>>)
                       -> InferCtxt<'a, 'tcx> {
        let mut infcx = InferCtxt::new(tcx, tables, None, false);
        infcx.normalize = true;
        infcx
    }

    /// Computes the least upper-bound of `a` and `b`. If this is not possible, reports an error and
    /// returns ty::err.
    pub fn common_supertype(&mut self,
                            origin: TypeOrigin,
                            a_is_expected: bool,
                            a: Ty<'tcx>,
                            b: Ty<'tcx>)
                            -> Ty<'tcx> {
        debug!("common_supertype({:?}, {:?})",
               a, b);

        let trace = TypeTrace {
            origin: origin,
            values: Types(expected_found(a_is_expected, a, b))
        };

        let result = self.commit_if_ok(|_,infcx| infcx.lub(a_is_expected, trace.clone()).relate(&a, &b));
        match result {
            Ok(t) => t,
            Err(ref err) => {
                self.report_and_explain_type_error(trace, err);
                self.tcx.types.err
            }
        }
    }

    pub fn mk_subty(&mut self,
                    a_is_expected: bool,
                    origin: TypeOrigin,
                    a: Ty<'tcx>,
                    b: Ty<'tcx>)
                    -> UnitResult<'tcx> {
        debug!("mk_subty({:?} <: {:?})", a, b);
        self.sub_types(a_is_expected, origin, a, b)
    }

    pub fn can_mk_subty(&mut self,
                        a: Ty<'tcx>,
                        b: Ty<'tcx>)
                        -> UnitResult<'tcx> {
        debug!("can_mk_subty({:?} <: {:?})", a, b);
        self.probe(|_, infer_ctxt| {
            let trace = TypeTrace {
                origin: TypeOrigin::Misc(codemap::DUMMY_SP),
                values: Types(expected_found(true, a, b))
            };
            infer_ctxt.sub(true, trace).relate(&a, &b).map(|_| ())
        })
    }

    pub fn can_mk_eqty(&mut self, a: Ty<'tcx>, b: Ty<'tcx>) -> UnitResult<'tcx> {
        self.can_equate(&a, &b)
    }

    pub fn mk_subr(&mut self,
                   origin: SubregionOrigin<'tcx>,
                   a: ty::Region,
                   b: ty::Region) {
        debug!("mk_subr({:?} <: {:?})", a, b);
        let snapshot = self.region_vars.start_snapshot();
        self.region_vars.make_subregion(origin, a, b);
        self.region_vars.commit(snapshot);
    }

    pub fn mk_eqty(&mut self,
                   a_is_expected: bool,
                   origin: TypeOrigin,
                   a: Ty<'tcx>,
                   b: Ty<'tcx>)
                   -> UnitResult<'tcx> {
        debug!("mk_eqty({:?} <: {:?})", a, b);
        self.commit_if_ok(|_,infcx| infcx.eq_types(a_is_expected, origin, a, b))
    }

    pub fn mk_sub_poly_trait_refs(&mut self,
                                  a_is_expected: bool,
                                  origin: TypeOrigin,
                                  a: ty::PolyTraitRef<'tcx>,
                                  b: ty::PolyTraitRef<'tcx>)
                                  -> UnitResult<'tcx> {
        debug!("mk_sub_trait_refs({:?} <: {:?})",
               a, b);
        self.commit_if_ok(|_,infcx|
               infcx.sub_poly_trait_refs(a_is_expected, origin, a.clone(), b.clone()))
    }

    pub fn freshen<T:TypeFoldable<'tcx>>(&mut self, t: T) -> T {
        let cell = RefCell::new(self);
        let mut freshener = TypeFreshener::new(&cell);
        t.fold_with(&mut freshener)
    }

    pub fn type_var_diverges(&self, ty: Ty) -> bool {
        match ty.sty {
            ty::TyInfer(ty::TyVar(vid)) => self.type_variables.borrow().var_diverges(vid),
            _ => false
        }
    }

    pub fn type_is_unconstrained_numeric(&self, ty: Ty) -> UnconstrainedNumeric {
        use middle::ty::error::UnconstrainedNumeric::Neither;
        use middle::ty::error::UnconstrainedNumeric::{UnconstrainedInt, UnconstrainedFloat};
        match ty.sty {
            ty::TyInfer(ty::IntVar(vid)) => {
                if self.int_unification_table.borrow_mut().has_value(vid) {
                    Neither
                } else {
                    UnconstrainedInt
                }
            },
            ty::TyInfer(ty::FloatVar(vid)) => {
                if self.float_unification_table.borrow_mut().has_value(vid) {
                    Neither
                } else {
                    UnconstrainedFloat
                }
            },
            _ => Neither,
        }
    }

    /// Returns a type variable's default fallback if any exists. A default
    /// must be attached to the variable when created, if it is created
    /// without a default, this will return None.
    ///
    /// This code does not apply to integral or floating point variables,
    /// only to use declared defaults.
    ///
    /// See `new_ty_var_with_default` to create a type variable with a default.
    /// See `type_variable::Default` for details about what a default entails.
    pub fn default(&self, ty: Ty<'tcx>) -> Option<type_variable::Default<'tcx>> {
        match ty.sty {
            ty::TyInfer(ty::TyVar(vid)) => self.type_variables.borrow().default(vid),
            _ => None
        }
    }

    pub fn unsolved_variables(&self) -> Vec<ty::Ty<'tcx>> {
        let mut variables = Vec::new();

        let unbound_ty_vars = self.type_variables
                                  .borrow()
                                  .unsolved_variables()
                                  .into_iter()
                                  .map(|t| self.tcx.mk_var(t));

        let unbound_int_vars = self.int_unification_table
                                   .borrow_mut()
                                   .unsolved_variables()
                                   .into_iter()
                                   .map(|v| self.tcx.mk_int_var(v));

        let unbound_float_vars = self.float_unification_table
                                     .borrow_mut()
                                     .unsolved_variables()
                                     .into_iter()
                                     .map(|v| self.tcx.mk_float_var(v));

        variables.extend(unbound_ty_vars);
        variables.extend(unbound_int_vars);
        variables.extend(unbound_float_vars);

        return variables;
    }

    fn combine_fields<'infcx>(&'infcx mut self, a_is_expected: bool, trace: TypeTrace<'tcx>)
                              -> CombineFields<'infcx, 'a, 'tcx> {
        CombineFields {
            infcx: Rc::new(RefCell::new(self)),
            a_is_expected: a_is_expected,
            trace: trace,
            cause: None,
        }
    }

    // public so that it can be used from the rustc_driver unit tests
    pub fn equate<'infcx>(&'infcx mut self, a_is_expected: bool, trace: TypeTrace<'tcx>)
              -> equate::Equate<'infcx, 'a, 'tcx>
    {
        self.combine_fields(a_is_expected, trace).equate()
    }

    // public so that it can be used from the rustc_driver unit tests
    pub fn sub<'infcx>(&'infcx mut self, a_is_expected: bool, trace: TypeTrace<'tcx>)
               -> sub::Sub<'infcx, 'a, 'tcx>
    {
        self.combine_fields(a_is_expected, trace).sub()
    }

    // public so that it can be used from the rustc_driver unit tests
    pub fn lub<'infcx>(&'infcx mut self, a_is_expected: bool, trace: TypeTrace<'tcx>)
               -> lub::Lub<'infcx, 'a, 'tcx>
    {
        self.combine_fields(a_is_expected, trace).lub()
    }

    // public so that it can be used from the rustc_driver unit tests
    pub fn glb<'infcx>(&'infcx mut self, a_is_expected: bool, trace: TypeTrace<'tcx>)
               -> glb::Glb<'infcx, 'a, 'tcx>
    {
        self.combine_fields(a_is_expected, trace).glb()
    }

    /// Execute `f` and commit only the region bindings if successful.
    /// The function f must be very careful not to leak any non-region
    /// variables that get created.
    pub fn commit_regions_if_ok<T, E, F>(&mut self, f: F) -> Result<T, E> where
        F: FnOnce() -> Result<T, E>
    {
        debug!("commit_regions_if_ok()");
        let CombinedSnapshot { type_snapshot,
                               int_snapshot,
                               float_snapshot,
                               region_vars_snapshot,
                               predicates_snapshot,
                               region_obligations_snapshot,
                               duplicate_set,
                             } = self.start_snapshot();

        let r = self.commit_if_ok(|_,_| f());

        debug!("commit_regions_if_ok: rolling back everything but regions");

        // Roll back any non-region bindings - they should be resolved
        // inside `f`, with, e.g. `resolve_type_vars_if_possible`.
        self.type_variables
            .borrow_mut()
            .rollback_to(type_snapshot);
        self.int_unification_table
            .borrow_mut()
            .rollback_to(int_snapshot);
        self.float_unification_table
            .borrow_mut()
            .rollback_to(float_snapshot);
        self.predicates.commit(predicates_snapshot);
        for (k, v) in region_obligations_snapshot {
            self.region_obligations.get_mut(&k).unwrap().commit(v);
        }

        // Commit region vars that may escape through resolved types.
        self.region_vars
            .commit(region_vars_snapshot);

        self.duplicate_set = duplicate_set;

        r
    }

    pub fn add_given(&self,
                     sub: ty::FreeRegion,
                     sup: ty::RegionVid)
    {
        self.region_vars.add_given(sub, sup);
    }

    pub fn sub_types(&mut self,
                     a_is_expected: bool,
                     origin: TypeOrigin,
                     a: Ty<'tcx>,
                     b: Ty<'tcx>)
                     -> UnitResult<'tcx>
    {
        debug!("sub_types({:?} <: {:?})", a, b);
        self.commit_if_ok(|_,infcx| {
            let trace = TypeTrace::types(origin, a_is_expected, a, b);
            infcx.sub(a_is_expected, trace).relate(&a, &b).map(|_| ())
        })
    }

    pub fn eq_types(&mut self,
                    a_is_expected: bool,
                    origin: TypeOrigin,
                    a: Ty<'tcx>,
                    b: Ty<'tcx>)
                    -> UnitResult<'tcx>
    {
        self.commit_if_ok(|_,infcx| {
            let trace = TypeTrace::types(origin, a_is_expected, a, b);
            infcx.equate(a_is_expected, trace).relate(&a, &b).map(|_| ())
        })
    }

    pub fn sub_trait_refs(&mut self,
                          a_is_expected: bool,
                          origin: TypeOrigin,
                          a: ty::TraitRef<'tcx>,
                          b: ty::TraitRef<'tcx>)
                          -> UnitResult<'tcx>
    {
        debug!("eq_trait_refs({:?} <: {:?})",
               a,
               b);
        self.commit_if_ok(|_, infcx| {
            let trace = TypeTrace {
                origin: origin,
                values: TraitRefs(expected_found(a_is_expected, a.clone(), b.clone()))
            };
            infcx.sub(a_is_expected, trace).relate(&a, &b).map(|_| ())
        })
    }

    pub fn sub_poly_trait_refs(&mut self,
                               a_is_expected: bool,
                               origin: TypeOrigin,
                               a: ty::PolyTraitRef<'tcx>,
                               b: ty::PolyTraitRef<'tcx>)
                               -> UnitResult<'tcx>
    {
        debug!("sub_poly_trait_refs({:?} <: {:?})",
               a,
               b);
        self.commit_if_ok(|_,infcx| {
            let trace = TypeTrace {
                origin: origin,
                values: PolyTraitRefs(expected_found(a_is_expected, a.clone(), b.clone()))
            };
            infcx.sub(a_is_expected, trace).relate(&a, &b).map(|_| ())
        })
    }

    pub fn skolemize_late_bound_regions<T>(&self,
                                           value: &ty::Binder<T>,
                                           snapshot: &CombinedSnapshot)
                                           -> (T, SkolemizationMap)
        where T : TypeFoldable<'tcx>
    {
        /*! See `higher_ranked::skolemize_late_bound_regions` */

        higher_ranked::skolemize_late_bound_regions(self, value, snapshot)
    }

    pub fn leak_check(&self,
                      skol_map: &SkolemizationMap,
                      snapshot: &CombinedSnapshot)
                      -> UnitResult<'tcx>
    {
        /*! See `higher_ranked::leak_check` */

        match higher_ranked::leak_check(self, skol_map, snapshot) {
            Ok(()) => Ok(()),
            Err((br, r)) => Err(TypeError::RegionsInsufficientlyPolymorphic(br, r))
        }
    }

    pub fn plug_leaks<T>(&mut self,
                         skol_map: SkolemizationMap,
                         snapshot: &CombinedSnapshot,
                         value: &T)
                         -> T
        where T : TypeFoldable<'tcx> + HasTypeFlags
    {
        /*! See `higher_ranked::plug_leaks` */

        higher_ranked::plug_leaks(self, skol_map, snapshot, value)
    }

    pub fn equality_predicate(&mut self,
                              span: Span,
                              predicate: &ty::PolyEquatePredicate<'tcx>)
                              -> UnitResult<'tcx> {
        self.commit_if_ok(|snapshot, infcx| {
            let (ty::EquatePredicate(a, b), skol_map) =
                infcx.skolemize_late_bound_regions(predicate, snapshot);
            let origin = TypeOrigin::EquatePredicate(span);
            let () = try!(infcx.mk_eqty(false, origin, a, b));
            infcx.leak_check(&skol_map, snapshot)
        })
    }

    pub fn region_outlives_predicate(&mut self,
                                     span: Span,
                                     predicate: &ty::PolyRegionOutlivesPredicate)
                                     -> UnitResult<'tcx> {
        self.commit_if_ok(|snapshot, infcx| {
            let (ty::OutlivesPredicate(r_a, r_b), skol_map) =
                infcx.skolemize_late_bound_regions(predicate, snapshot);
            let origin = RelateRegionParamBound(span);
            let () = infcx.mk_subr(origin, r_b, r_a); // `b : a` ==> `a <= b`
            infcx.leak_check(&skol_map, snapshot)
        })
    }

    pub fn next_ty_var_id(&self, diverging: bool) -> TyVid {
        self.type_variables
            .borrow_mut()
            .new_var(diverging, None)
    }

    pub fn next_ty_var(&self) -> Ty<'tcx> {
        self.tcx.mk_var(self.next_ty_var_id(false))
    }

    pub fn next_ty_var_with_default(&self,
                                    default: Option<type_variable::Default<'tcx>>) -> Ty<'tcx> {
        let ty_var_id = self.type_variables
                            .borrow_mut()
                            .new_var(false, default);

        self.tcx.mk_var(ty_var_id)
    }

    pub fn next_diverging_ty_var(&self) -> Ty<'tcx> {
        self.tcx.mk_var(self.next_ty_var_id(true))
    }

    pub fn next_ty_vars(&self, n: usize) -> Vec<Ty<'tcx>> {
        (0..n).map(|_i| self.next_ty_var()).collect()
    }

    pub fn next_int_var_id(&self) -> IntVid {
        self.int_unification_table
            .borrow_mut()
            .new_key(None)
    }

    pub fn next_float_var_id(&self) -> FloatVid {
        self.float_unification_table
            .borrow_mut()
            .new_key(None)
    }

    pub fn next_region_var(&self, origin: RegionVariableOrigin) -> ty::Region {
        ty::ReVar(self.region_vars.new_region_var(origin))
    }

    pub fn region_vars_for_defs(&self,
                                span: Span,
                                defs: &[ty::RegionParameterDef])
                                -> Vec<ty::Region> {
        defs.iter()
            .map(|d| self.next_region_var(EarlyBoundRegion(span, d.name)))
            .collect()
    }

    // We have to take `&mut Substs` in order to provide the correct substitutions for defaults
    // along the way, for this reason we don't return them.
    pub fn type_vars_for_defs(&self,
                              span: Span,
                              space: subst::ParamSpace,
                              substs: &mut Substs<'tcx>,
                              defs: &[ty::TypeParameterDef<'tcx>]) {

        let mut vars = Vec::with_capacity(defs.len());

        for def in defs.iter() {
            let default = def.default.map(|default| {
                type_variable::Default {
                    ty: default.subst_spanned(self.tcx, substs, Some(span)),
                    origin_span: span,
                    def_id: def.default_def_id
                }
            });

            let ty_var = self.next_ty_var_with_default(default);
            substs.types.push(space, ty_var);
            vars.push(ty_var)
        }
    }

    /// Given a set of generics defined on a type or impl, returns a substitution mapping each
    /// type/region parameter to a fresh inference variable.
    pub fn fresh_substs_for_generics(&self,
                                     span: Span,
                                     generics: &ty::Generics<'tcx>)
                                     -> subst::Substs<'tcx>
    {
        let type_params = subst::VecPerParamSpace::empty();

        let region_params =
            generics.regions.map(
                |d| self.next_region_var(EarlyBoundRegion(span, d.name)));

        let mut substs = subst::Substs::new(type_params, region_params);

        for space in subst::ParamSpace::all().iter() {
            self.type_vars_for_defs(
                span,
                *space,
                &mut substs,
                generics.types.get_slice(*space));
        }

        return substs;
    }

    /// Given a set of generics defined on a trait, returns a substitution mapping each output
    /// type/region parameter to a fresh inference variable, and mapping the self type to
    /// `self_ty`.
    pub fn fresh_substs_for_trait(&self,
                                  span: Span,
                                  generics: &ty::Generics<'tcx>,
                                  self_ty: Ty<'tcx>)
                                  -> subst::Substs<'tcx>
    {

        assert!(generics.types.len(subst::SelfSpace) == 1);
        assert!(generics.types.len(subst::FnSpace) == 0);
        assert!(generics.regions.len(subst::SelfSpace) == 0);
        assert!(generics.regions.len(subst::FnSpace) == 0);

        let type_params = Vec::new();

        let region_param_defs = generics.regions.get_slice(subst::TypeSpace);
        let regions = self.region_vars_for_defs(span, region_param_defs);

        let mut substs = subst::Substs::new_trait(type_params, regions, self_ty);

        let type_parameter_defs = generics.types.get_slice(subst::TypeSpace);
        self.type_vars_for_defs(span, subst::TypeSpace, &mut substs, type_parameter_defs);

        return substs;
    }

    pub fn fresh_bound_region(&self, debruijn: ty::DebruijnIndex) -> ty::Region {
        self.region_vars.new_bound(debruijn)
    }

    /// Apply `adjustment` to the type of `expr`
    pub fn adjust_expr_ty(&mut self,
                          expr: &hir::Expr,
                          adjustment: Option<&adjustment::AutoAdjustment<'tcx>>)
                          -> Ty<'tcx>
    {
        let raw_ty = self.expr_ty(expr);
        let raw_ty = self.shallow_resolve(raw_ty);
        raw_ty.adjust(self.tcx,
                      expr.span,
                      expr.id,
                      adjustment,
                      |method_call| self.tables
                                        .borrow()
                                        .method_map
                                        .get(&method_call)
                      .map(|method|
                           self.resolve_type_vars_if_possible(&method.ty)))
    }

    pub fn node_type(&self, id: ast::NodeId) -> Ty<'tcx> {
        match self.tables.borrow().node_types.get(&id) {
            Some(&t) => t,
            // FIXME
            None if self.tcx.sess.err_count() - self.err_count_on_creation != 0 =>
                self.tcx.types.err,
            None => {
                self.tcx.sess.bug(
                    &format!("no type for node {}: {} in fcx",
                            id, self.tcx.map.node_to_string(id)));
            }
        }
    }

    pub fn expr_ty(&self, ex: &hir::Expr) -> Ty<'tcx> {
        match self.tables.borrow().node_types.get(&ex.id) {
            Some(&t) => t,
            None => {
                self.tcx.sess.bug("no type for expr in fcx");
            }
        }
    }

    pub fn resolve_regions_and_report_errors(&mut self,
                                             free_regions: &FreeRegionMap,
                                             subject_node_id: ast::NodeId) {
        let errors = self.region_vars.resolve_regions(free_regions, subject_node_id);
        self.report_region_errors(&errors); // see error_reporting.rs
    }

    pub fn ty_to_string(&mut self, t: Ty<'tcx>) -> String {
        self.resolve_type_vars_if_possible(&t).to_string()
    }

    pub fn tys_to_string(&mut self, ts: &[Ty<'tcx>]) -> String {
        let tstrs: Vec<String> = ts.iter().map(|t| self.ty_to_string(*t)).collect();
        format!("({})", tstrs.join(", "))
    }

    pub fn trait_ref_to_string(&mut self, t: &ty::TraitRef<'tcx>) -> String {
        self.resolve_type_vars_if_possible(t).to_string()
    }

    pub fn shallow_resolve(&self, typ: Ty<'tcx>) -> Ty<'tcx> {
        match typ.sty {
            ty::TyInfer(ty::TyVar(v)) => {
                // Not entirely obvious: if `typ` is a type variable,
                // it can be resolved to an int/float variable, which
                // can then be recursively resolved, hence the
                // recursion. Note though that we prevent type
                // variables from unifying to other type variables
                // directly (though they may be embedded
                // structurally), and we prevent cycles in any case,
                // so this recursion should always be of very limited
                // depth.
                self.type_variables.borrow()
                    .probe(v)
                    .map(|t| self.shallow_resolve(t))
                    .unwrap_or(typ)
            }

            ty::TyInfer(ty::IntVar(v)) => {
                self.int_unification_table
                    .borrow_mut()
                    .probe(v)
                    .map(|v| v.to_type(self.tcx))
                    .unwrap_or(typ)
            }

            ty::TyInfer(ty::FloatVar(v)) => {
                self.float_unification_table
                    .borrow_mut()
                    .probe(v)
                    .map(|v| v.to_type(self.tcx))
                    .unwrap_or(typ)
            }

            _ => {
                typ
            }
        }
    }

    pub fn resolve_type_vars_if_possible<T>(&self, value: &T) -> T
        where T: TypeFoldable<'tcx> + HasTypeFlags
    {
        /*!
         * Where possible, replaces type/int/float variables in
         * `value` with their final value. Note that region variables
         * are unaffected. If a type variable has not been unified, it
         * is left as is.  This is an idempotent operation that does
         * not affect inference state in any way and so you can do it
         * at will.
         */

        if !value.needs_infer() {
            return value.clone(); // avoid duplicated subst-folding
        }
        let mut r = resolve::OpportunisticTypeResolver::new(self);
        value.fold_with(&mut r)
    }

    pub fn resolve_type_and_region_vars_if_possible<T>(&self, value: &T) -> T
        where T: TypeFoldable<'tcx>
    {
        let mut r = resolve::OpportunisticTypeAndRegionResolver::new(self);
        value.fold_with(&mut r)
    }

    /// Resolves all type variables in `t` and then, if any were left
    /// unresolved, substitutes an error type. This is used after the
    /// main checking when doing a second pass before writeback. The
    /// justification is that writeback will produce an error for
    /// these unconstrained type variables.
    fn resolve_type_vars_or_error(&mut self, t: &Ty<'tcx>) -> mc::McResult<Ty<'tcx>> {
        let ty = self.resolve_type_vars_if_possible(t);
        if ty.references_error() || ty.is_ty_var() {
            debug!("resolve_type_vars_or_error: error from {:?}", ty);
            Err(())
        } else {
            Ok(ty)
        }
    }

    pub fn fully_resolve<T:TypeFoldable<'tcx>>(&self, value: &T) -> FixupResult<T> {
        /*!
         * Attempts to resolve all type/region variables in
         * `value`. Region inference must have been run already (e.g.,
         * by calling `resolve_regions_and_report_errors`).  If some
         * variable was never unified, an `Err` results.
         *
         * This method is idempotent, but it not typically not invoked
         * except during the writeback phase.
         */

        resolve::fully_resolve(self, value)
    }

    // [Note-Type-error-reporting]
    // An invariant is that anytime the expected or actual type is TyError (the special
    // error type, meaning that an error occurred when typechecking this expression),
    // this is a derived error. The error cascaded from another error (that was already
    // reported), so it's not useful to display it to the user.
    // The following four methods -- type_error_message_str, type_error_message_str_with_expected,
    // type_error_message, and report_mismatched_types -- implement this logic.
    // They check if either the actual or expected type is TyError, and don't print the error
    // in this case. The typechecker should only ever report type errors involving mismatched
    // types using one of these four methods, and should not call span_err directly for such
    // errors.
    pub fn type_error_message_str<M>(&mut self,
                                     sp: Span,
                                     mk_msg: M,
                                     actual_ty: String,
                                     err: Option<&TypeError<'tcx>>)
        where M: FnOnce(Option<String>, String) -> String,
    {
        self.type_error_message_str_with_expected(sp, mk_msg, None, actual_ty, err)
    }

    pub fn type_error_struct_str<M>(&self,
                                    sp: Span,
                                    mk_msg: M,
                                    actual_ty: String,
                                    err: Option<&TypeError<'tcx>>)
                                    -> DiagnosticBuilder<'tcx>
        where M: FnOnce(Option<String>, String) -> String,
    {
        self.type_error_struct_str_with_expected(sp, mk_msg, None, actual_ty, err)
    }

    pub fn type_error_message_str_with_expected<M>(&self,
                                                   sp: Span,
                                                   mk_msg: M,
                                                   expected_ty: Option<Ty<'tcx>>,
                                                   actual_ty: String,
                                                   err: Option<&TypeError<'tcx>>)
        where M: FnOnce(Option<String>, String) -> String,
    {
        self.type_error_struct_str_with_expected(sp, mk_msg, expected_ty, actual_ty, err)
            .emit();
    }

    pub fn type_error_struct_str_with_expected<M>(&self,
                                                  sp: Span,
                                                  mk_msg: M,
                                                  expected_ty: Option<Ty<'tcx>>,
                                                  actual_ty: String,
                                                  err: Option<&TypeError<'tcx>>)
                                                  -> DiagnosticBuilder<'tcx>
        where M: FnOnce(Option<String>, String) -> String,
    {
        debug!("hi! expected_ty = {:?}, actual_ty = {}", expected_ty, actual_ty);

        let resolved_expected = expected_ty.map(|e_ty| self.resolve_type_vars_if_possible(&e_ty));

        if !resolved_expected.references_error() {
            let error_str = err.map_or("".to_string(), |t_err| {
                format!(" ({})", t_err)
            });

            let mut db = self.tcx.sess.struct_span_err(sp, &format!("{}{}",
                mk_msg(resolved_expected.map(|t| self.ty_to_string(t)), actual_ty),
                error_str));

            if let Some(err) = err {
                self.tcx.note_and_explain_type_err(&mut db, err, sp);
            }
            db
        } else {
            self.tcx.sess.diagnostic().struct_dummy()
        }
    }

    pub fn type_error_message<M>(&mut self,
                                 sp: Span,
                                 mk_msg: M,
                                 actual_ty: Ty<'tcx>,
                                 err: Option<&TypeError<'tcx>>)
        where M: FnOnce(String) -> String,
    {
        self.type_error_struct(sp, mk_msg, actual_ty, err).emit();
    }

    pub fn type_error_struct<M>(&self,
                                sp: Span,
                                mk_msg: M,
                                actual_ty: Ty<'tcx>,
                                err: Option<&TypeError<'tcx>>)
                                -> DiagnosticBuilder<'tcx>
        where M: FnOnce(String) -> String,
    {
        let actual_ty = self.resolve_type_vars_if_possible(&actual_ty);

        // Don't report an error if actual type is TyError.
        if actual_ty.references_error() {
            return self.tcx.sess.diagnostic().struct_dummy();
        }

        self.type_error_struct_str(sp,
            move |_e, a| { mk_msg(a) },
            self.ty_to_string(actual_ty), err)
    }

    pub fn report_mismatched_types(&mut self,
                                   span: Span,
                                   expected: Ty<'tcx>,
                                   actual: Ty<'tcx>,
                                   err: &TypeError<'tcx>) {
        let trace = TypeTrace {
            origin: TypeOrigin::Misc(span),
            values: Types(ExpectedFound {
                expected: expected,
                found: actual
            })
        };
        self.report_and_explain_type_error(trace, err);
    }

    pub fn report_conflicting_default_types(&mut self,
                                            span: Span,
                                            expected: type_variable::Default<'tcx>,
                                            actual: type_variable::Default<'tcx>) {
        let trace = TypeTrace {
            origin: TypeOrigin::Misc(span),
            values: Types(ExpectedFound {
                expected: expected.ty,
                found: actual.ty
            })
        };

        self.report_and_explain_type_error(trace,
            &TypeError::TyParamDefaultMismatch(ExpectedFound {
                expected: expected,
                found: actual
        }));
    }

    pub fn replace_late_bound_regions_with_fresh_var<T>(
        &self,
        span: Span,
        lbrct: LateBoundRegionConversionTime,
        value: &ty::Binder<T>)
        -> (T, FnvHashMap<ty::BoundRegion,ty::Region>)
        where T : TypeFoldable<'tcx>
    {
        self.tcx.replace_late_bound_regions(
            value,
            |br| self.next_region_var(LateBoundRegion(span, br, lbrct)))
    }

    /// See `verify_generic_bound` method in `region_inference`
    pub fn verify_generic_bound(&self,
                                origin: SubregionOrigin<'tcx>,
                                kind: GenericKind<'tcx>,
                                a: ty::Region,
                                bound: VerifyBound) {
        debug!("verify_generic_bound({:?}, {:?} <: {:?})",
               kind,
               a,
               bound);

        self.region_vars.verify_generic_bound(origin, kind, a, bound);
    }

    pub fn can_equate<T>(&mut self, a: &T, b: &T) -> UnitResult<'tcx>
        where T: Relate<'a,'tcx> + fmt::Debug
    {
        debug!("can_equate({:?}, {:?})", a, b);
        self.probe(|_,infcx| {
            // Gin up a dummy trace, since this won't be committed
            // anyhow. We should make this typetrace stuff more
            // generic so we don't have to do anything quite this
            // terrible.
            let e = infcx.tcx.types.err;
            let trace = TypeTrace {
                origin: TypeOrigin::Misc(codemap::DUMMY_SP),
                values: Types(expected_found(true, e, e))
            };
            infcx.equate(true, trace).relate(a, b).map(|_| ())
        })
    }

    pub fn node_ty(&mut self, id: ast::NodeId) -> McResult<Ty<'tcx>> {
        let ty = self.node_type(id);
        self.resolve_type_vars_or_error(&ty)
    }

    pub fn expr_ty_adjusted(&mut self, expr: &hir::Expr) -> McResult<Ty<'tcx>> {
        let ty = self.adjust_expr_ty(expr, self.tables.borrow().adjustments.get(&expr.id));
        self.resolve_type_vars_or_error(&ty)
    }

    pub fn tables_are_tcx_tables(&self) -> bool {
        let tables: &RefCell<ty::Tables> = &self.tables;
        let tcx_tables: &RefCell<ty::Tables> = &self.tcx.tables;
        tables as *const _ == tcx_tables as *const _
    }

    pub fn type_moves_by_default(&mut self, ty: Ty<'tcx>, span: Span) -> bool {
        let ty = self.resolve_type_vars_if_possible(&ty);
        if ty.needs_infer() ||
            (ty.has_closure_types() && !self.tables_are_tcx_tables()) {
            // this can get called from typeck (by euv), and moves_by_default
            // rightly refuses to work with inference variables, but
            // moves_by_default has a cache, which we want to use in other
            // cases.
            !traits::type_known_to_meet_builtin_bound(self, ty, ty::BoundCopy, span)
        } else {
            ty.moves_by_default(&self.parameter_environment, span)
        }
    }

    pub fn node_method_ty(&mut self, method_call: ty::MethodCall)
                          -> Option<Ty<'tcx>> {
        self.tables
            .borrow()
            .method_map
            .get(&method_call)
            .map(|method| method.ty)
            .map(|ty| self.resolve_type_vars_if_possible(&ty))
    }

    pub fn node_method_id(&self, method_call: ty::MethodCall)
                          -> Option<DefId> {
        self.tables
            .borrow()
            .method_map
            .get(&method_call)
            .map(|method| method.def_id)
    }
    pub fn adjustments(&self) -> Ref<NodeMap<adjustment::AutoAdjustment<'tcx>>> {
        Ref::map(self.tables.borrow(), |tables| &tables.adjustments)
    }

    pub fn is_method_call(&self, id: ast::NodeId) -> bool {
        self.tables.borrow().method_map.contains_key(&ty::MethodCall::expr(id))
    }

    pub fn temporary_scope(&self, rvalue_id: ast::NodeId) -> Option<CodeExtent> {
        self.tcx.region_maps.temporary_scope(rvalue_id)
    }

    pub fn upvar_capture(&self, upvar_id: ty::UpvarId) -> Option<ty::UpvarCapture> {
        self.tables.borrow().upvar_capture_map.get(&upvar_id).cloned()
    }

    pub fn param_env<'b>(&'b self) -> &'b ty::ParameterEnvironment<'a,'tcx> {
        &self.parameter_environment
    }

    pub fn closure_kind(&self,
                        def_id: DefId)
                        -> Option<ty::ClosureKind>
    {
        if def_id.is_local() {
            self.tables.borrow().closure_kinds.get(&def_id).cloned()
        } else {
            // During typeck, ALL closures are local. But afterwards,
            // during trans, we see closure ids from other traits.
            // That may require loading the closure data out of the
            // cstore.
            Some(ty::Tables::closure_kind(&self.tables, self.tcx, def_id))
        }
    }

    pub fn closure_type(&self,
                        def_id: DefId,
                        substs: &ty::ClosureSubsts<'tcx>)
                        -> ty::ClosureTy<'tcx>
    {
        let closure_ty =
            ty::Tables::closure_type(self.tables,
                                     self.tcx,
                                     def_id,
                                     substs);

        if self.normalize {
            normalize_associated_type(&self.tcx, &closure_ty)
        } else {
            closure_ty
        }
    }

    pub fn drain_fulfillment_cx_or_panic<T>(&'a mut self, result: &T, span: Span) -> T
        where T : TypeFoldable<'tcx>
    {
        match self.drain_fulfillment_cx(result) {
            Ok(v) => v,
            Err(errors) => {
                self.tcx.sess.span_bug(
                    span,
                    &format!("Encountered errors `{:?}` fulfilling during trans",
                             errors));
            }
        }
    }

    /// Finishes processes any obligations that remain in the fulfillment
    /// context, and then "freshens" and returns `result`. This is
    /// primarily used during normalization and other cases where
    /// processing the obligations in `fulfill_cx` may cause type
    /// inference variables that appear in `result` to be unified, and
    /// hence we need to process those obligations to get the complete
    /// picture of the type.
    pub fn drain_fulfillment_cx<T>(&'a mut self, result: &T)
                                   -> Result<T,Vec<traits::FulfillmentError<'tcx>>>
        where T : TypeFoldable<'tcx>
    {
        debug!("drain_fulfillment_cx(result={:?})",
               result);

        // In principle, we only need to do this so long as `result`
        // contains unbound type parameters. It could be a slight
        // optimization to stop iterating early.
        match self.select_all_or_error() {
            Ok(()) => { }
            Err(errors) => {
                return Err(errors);
            }
        }

        // Use freshen to simultaneously replace all type variables with
        // their bindings and replace all regions with 'static.  This is
        // sort of overkill because we do not expect there to be any
        // unbound type variables, hence no `TyFresh` types should ever be
        // inserted.
        let cell = RefCell::new(self);
        let mut freshener = TypeFreshener::new(&cell);
        Ok(result.fold_with(&mut freshener))
    }

    // Emulates the old style of creating a fresh fulfillment context. This allows us to prove only
    // this set of obligations registered by `f`.
    pub fn select_only<R, F: FnOnce(&mut InferCtxt<'a, 'tcx>) -> R>(&mut self, f: F)-> Result<R,Vec<FulfillmentError<'tcx>>> {
        let mut other_predicates = SnapshotTree::new();
        mem::swap(&mut other_predicates, &mut self.predicates);

        let value = f(self);

        let result = self.select_all_or_error().map(|_| value);

        mem::swap(&mut other_predicates, &mut self.predicates);

        result
    }

    pub fn select_all_or_error(&mut self) -> Result<(),Vec<FulfillmentError<'tcx>>> {
        try!(self.select_where_possible());

        // Refactor this to not need internal fulfillment ctxt details
        // Anything left is ambiguous.
        let errors: Vec<FulfillmentError> =
            self.predicates
                .nodes()
                .map(|n| &n.elem)
                .filter(|p| !p.is_complete())
                .map(|p| FulfillmentError::new(p.obligation.clone(), CodeAmbiguity))
                .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Attempts to select obligations that were registered since the call to a selection routine.
    /// This is used by the type checker to eagerly attempt to resolve obligations in hopes of
    /// gaining type information. It'd be equally valid to use `select_where_possible` but it
    /// results in `O(n^2)` performance (#18208).
    pub fn select_new_obligations(&mut self)
                                      -> Result<(),Vec<FulfillmentError<'tcx>>> {
        let cell = RefCell::new(self);
        let mut selcx = SelectionContext::new(&cell);
        InferCtxt::select(&mut selcx, true)
    }

    pub fn select_where_possible(&mut self) -> Result<(),Vec<FulfillmentError<'tcx>>> {
        let cell = RefCell::new(self);
        let mut selcx = SelectionContext::new(&cell);
        InferCtxt::select(&mut selcx, false)
    }

    /// Attempts to select obligations using `selcx`. If `only_new_obligations` is true, then it
    /// only attempts to select obligations that haven't been seen before.
    pub fn select<'cell, 'infcx>(selcx: &mut SelectionContext<'cell, 'infcx, 'a, 'tcx>,
                                 only_new_obligations: bool)
                                 -> Result<(),Vec<FulfillmentError<'tcx>>> {

        debug!("select({} obligations, only_new_obligations={}) start",
            selcx.infcx().predicates.len(),
            only_new_obligations);

        let mut errors = Vec::new();

        loop {
            let count = selcx.infcx().pending_obligations().len();

            debug!("select_where_possible({} obligations) iteration",
                   count);

            let mut new_obligations = Vec::new();

            // // If we are only attempting obligations we haven't seen yet,
            // // then set `skip` to the number of obligations we've already
            // // seen.
            // let mut skip = if only_new_obligations {
            //     self.attempted_mark
            // } else {
            //     0
            // };

            // First pass: walk each obligation, retaining
            // only those that we cannot yet process.

            let total_predicates = selcx.infcx().predicates.len();

            for obligation_id in (0..total_predicates) {
                let _ = process_predicate(
                    selcx,
                    obligation_id as u32,
                    &mut new_obligations,
                    &mut errors);
            }

            let attempted_mark = selcx.infcx().predicates.len();
            selcx.infcx().attempted_mark = attempted_mark;

            if selcx.infcx().pending_obligations().len() == count {
                // Nothing changed.
                break;
            }
            // Now go through all the successful ones,
            // registering any nested obligations for the future.
            for new_obligation in new_obligations {
                selcx.infcx().register_predicate_obligation(new_obligation);
            }
        }

        debug!("select({} obligations, {} errors) done",
               selcx.infcx().predicates.len(),
               errors.len());

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// "Normalize" a projection type `<SomeType as SomeTrait>::X` by
    /// creating a fresh type variable `$0` as well as a projection
    /// predicate `<SomeType as SomeTrait>::X == $0`. When the
    /// inference engine runs, it will attempt to find an impl of
    /// `SomeTrait` or a where clause that lets us unify `$0` with
    /// something concrete. If this fails, we'll unify `$0` with
    /// `projection_ty` again.
    pub fn normalize_projection_type(&mut self,
                                     projection_ty: ty::ProjectionTy<'tcx>,
                                     cause: ObligationCause<'tcx>)
                                     -> Ty<'tcx>
    {
        debug!("normalize_associated_type(projection_ty={:?})",
               projection_ty);

        assert!(!projection_ty.has_escaping_regions());


        let normalized = project::scoped_selcx(self, |mut selcx| {
            project::normalize_projection_type(&mut selcx, projection_ty, cause, 0)
        });

        for obligation in normalized.obligations {
            self.register_predicate_obligation(obligation);
        }

        debug!("normalize_associated_type: result={:?}", normalized.value);

        normalized.value
    }

    pub fn register_builtin_bound(&mut self,
                                  ty: Ty<'tcx>,
                                  builtin_bound: ty::BuiltinBound,
                                  cause: ObligationCause<'tcx>)
    {
        match predicate_for_builtin_bound(self.tcx, cause, builtin_bound, 0, ty) {
            Ok(predicate) => {
                self.register_predicate_obligation(predicate)
            }
            Err(ErrorReported) => {}
        }
    }

    pub fn register_predicate_obligation(&mut self,
                                         obligation: PredicateObligation<'tcx>) {
        // this helps to reduce duplicate errors, as well as making
        // debug output much nicer to read and so on.
        let obligation = self.resolve_type_vars_if_possible(&obligation);

        assert!(!obligation.has_escaping_regions());

        let w = RFC1214Warning(obligation.cause.code.is_rfc1214());

        if self.is_duplicate_or_add(self.tcx, w, &obligation.predicate) {
            debug!("register_predicate({:?}) -- already seen, skip", obligation);
            return;
        }

        debug!("register_predicate({:?})", obligation);
        self.predicates.insert_root(PendingPredicateObligation::new(obligation));
    }

    pub fn register_region_obligation(&mut self,
                                      t_a: Ty<'tcx>,
                                      r_b: ty::Region,
                                      cause: ObligationCause<'tcx>)
    {
        register_region_obligation(
            t_a, r_b,
            cause,
            &mut self.region_obligations);
    }

    pub fn region_obligations(&self,
                              body_id: ast::NodeId)
                              -> &[RegionObligation<'tcx>]
    {
        match self.region_obligations.get(&body_id) {
            None => Default::default(),
            Some(vec) => vec,
        }
    }

    pub fn pending_obligations(&mut self) -> Vec<&PredicateObligation<'tcx>> {
        self.predicates
            .nodes()
            .filter(|n| !n.elem.is_complete())
            .map(|n| &n.elem.obligation)
            .collect()
    }

    fn is_duplicate_or_add(&mut self,
                           tcx: &ty::ctxt<'tcx>,
                           w: RFC1214Warning,
                           predicate: &ty::Predicate<'tcx>)
                           -> bool {
        // This is a kind of dirty hack to allow us to avoid "rederiving"
        // things that we have already proven in other methods.
        //
        // The idea is that any predicate that doesn't involve type
        // parameters and which only involves the 'static region (and
        // no other regions) is universally solvable, since impls are global.
        //
        // This is particularly important since even if we have a
        // cache hit in the selection context, we still wind up
        // evaluating the 'nested obligations'.  This cache lets us
        // skip those.

        let will_warn_due_to_rfc1214 = w.0;
        let errors_will_be_reported = self.errors_will_be_reported && !will_warn_due_to_rfc1214;
        if errors_will_be_reported && predicate.is_global() {
            tcx.fulfilled_predicates.borrow_mut().is_duplicate_or_add(w, predicate)
        } else {
            self.duplicate_set.is_duplicate_or_add(w, predicate)
        }
    }
}

fn register_region_obligation<'tcx>(t_a: Ty<'tcx>,
                                    r_b: ty::Region,
                                    cause: ObligationCause<'tcx>,
                                    region_obligations: &mut NodeMap<SnapshotVec<RegionObligation<'tcx>>>) {
    let region_obligation = RegionObligation { sup_type: t_a,
                                               sub_region: r_b,
                                               cause: cause };

   debug!("register_region_obligation({:?})",
         region_obligation);

    region_obligations.entry(region_obligation.cause.body_id).or_insert(SnapshotVec::new())
        .push(region_obligation);
}


fn process_predicate<'cell, 'infcx, 'cx, 'tcx>(selcx: &mut SelectionContext<'cell, 'infcx, 'cx, 'tcx>,
                                               obligation_id: u32,
                                               new_obligations: &mut Vec<PredicateObligation<'tcx>>,
                                               errors: &mut Vec<FulfillmentError<'tcx>>)
                                               -> bool
{
    /*!
     * Processes a predicate obligation and modifies the appropriate
     * output array with the successful/error result.  Returns `false`
     * if the predicate could not be processed due to insufficient
     * type inference.
     */
    // Remove clones, trying to get this to compile.
    let predicate = selcx.infcx().predicates.get(obligation_id).clone();

    if predicate.is_complete() {
        return true;
    }

    let obligation = predicate.obligation;

    let is_complete = match obligation.predicate {
        ty::Predicate::Trait(ref data) => {
            let trait_obligation = obligation.with(data.clone());
            match selcx.select(&trait_obligation) {
                Ok(None) => {
                    false
                }
                Ok(Some(s)) => {
                    new_obligations.append(&mut s.nested_obligations());
                    true
                }
                Err(selection_err) => {
                    debug!("predicate: {:?} error: {:?}",
                           obligation,
                           selection_err);
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeSelectionError(selection_err)));
                    true
                }
            }
        }

        ty::Predicate::Equate(ref binder) => {
            match selcx.infcx().equality_predicate(obligation.cause.span, binder) {
                Ok(()) => { }
                Err(_) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeSelectionError(Unimplemented)));
                }
            }
            true
        }

        ty::Predicate::RegionOutlives(ref binder) => {
            match selcx.infcx().region_outlives_predicate(obligation.cause.span, binder) {
                Ok(()) => { }
                Err(_) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeSelectionError(Unimplemented)));
                }
            }

            true
        }

        ty::Predicate::TypeOutlives(ref binder) => {
            // Check if there are higher-ranked regions.
            match selcx.tcx().no_late_bound_regions(binder) {
                // If there are, inspect the underlying type further.
                None => {
                    // Convert from `Binder<OutlivesPredicate<Ty, Region>>` to `Binder<Ty>`.
                    let binder = binder.map_bound_ref(|pred| pred.0);

                    // Check if the type has any bound regions.
                    match selcx.tcx().no_late_bound_regions(&binder) {
                        // If so, this obligation is an error (for now). Eventually we should be
                        // able to support additional cases here, like `for<'a> &'a str: 'a`.
                        None => {
                            errors.push(
                                FulfillmentError::new(
                                    obligation.clone(),
                                    CodeSelectionError(Unimplemented)))
                        }
                        // Otherwise, we have something of the form
                        // `for<'a> T: 'a where 'a not in T`, which we can treat as `T: 'static`.
                        Some(t_a) => {
                            register_region_obligation(t_a, ty::ReStatic,
                                                       obligation.cause.clone(),
                                                       &mut selcx.infcx().region_obligations);
                        }
                    }
                }
                // If there aren't, register the obligation.
                Some(ty::OutlivesPredicate(t_a, r_b)) => {
                    register_region_obligation(t_a, r_b,
                                               obligation.cause.clone(),
                                               &mut selcx.infcx().region_obligations);
                }
            }
            true
        }

        ty::Predicate::Projection(ref data) => {
            let project_obligation = obligation.with(data.clone());
            let result = project::poly_project_and_unify_type(selcx, &project_obligation);
            debug!("process_predicate: poly_project_and_unify_type({:?}) returned {:?}",
                   project_obligation,
                   result);
            match result {
                Ok(Some(obligations)) => {
                    new_obligations.extend(obligations);
                    true
                }
                Ok(None) => {
                    false
                }
                Err(err) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeProjectionError(err)));
                    true
                }
            }
        }

        ty::Predicate::ObjectSafe(trait_def_id) => {
            if !is_object_safe(selcx.tcx(), trait_def_id) {
                errors.push(FulfillmentError::new(
                    obligation.clone(),
                    CodeSelectionError(Unimplemented)));
            }
            true
        }

        ty::Predicate::WellFormed(ty) => {
            let rfc1214 = match obligation.cause.code {
                ObligationCauseCode::RFC1214(_) => true,
                _ => false,
            };
            match ty::wf::obligations(&mut selcx.infcx(), obligation.cause.body_id,
                                      ty, obligation.cause.span, rfc1214) {
                Some(obligations) => {
                    new_obligations.extend(obligations);
                    true
                }
                None => {
                    false
                }
            }
        }
    };

    if is_complete {
        info!("completing predicate obligation_id={}", obligation_id);
        selcx.infcx().predicates.get_mut(obligation_id).complete();
        info!("predicate: {:?}", selcx.infcx().predicates.get(obligation_id).complete);
    }

    return is_complete;
}

impl<'tcx> TypeTrace<'tcx> {
    pub fn span(&self) -> Span {
        self.origin.span()
    }

    pub fn types(origin: TypeOrigin,
                 a_is_expected: bool,
                 a: Ty<'tcx>,
                 b: Ty<'tcx>)
                 -> TypeTrace<'tcx> {
        TypeTrace {
            origin: origin,
            values: Types(expected_found(a_is_expected, a, b))
        }
    }

    pub fn dummy(tcx: &ty::ctxt<'tcx>) -> TypeTrace<'tcx> {
        TypeTrace {
            origin: TypeOrigin::Misc(codemap::DUMMY_SP),
            values: Types(ExpectedFound {
                expected: tcx.types.err,
                found: tcx.types.err,
            })
        }
    }
}

impl<'tcx> fmt::Debug for TypeTrace<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TypeTrace({:?})", self.origin)
    }
}

impl TypeOrigin {
    pub fn span(&self) -> Span {
        match *self {
            TypeOrigin::MethodCompatCheck(span) => span,
            TypeOrigin::ExprAssignable(span) => span,
            TypeOrigin::Misc(span) => span,
            TypeOrigin::RelateTraitRefs(span) => span,
            TypeOrigin::RelateSelfType(span) => span,
            TypeOrigin::RelateOutputImplTypes(span) => span,
            TypeOrigin::MatchExpressionArm(match_span, _, _) => match_span,
            TypeOrigin::IfExpression(span) => span,
            TypeOrigin::IfExpressionWithNoElse(span) => span,
            TypeOrigin::RangeExpression(span) => span,
            TypeOrigin::EquatePredicate(span) => span,
        }
    }
}

impl<'tcx> SubregionOrigin<'tcx> {
    pub fn span(&self) -> Span {
        match *self {
            Subtype(ref a) => a.span(),
            InfStackClosure(a) => a,
            InvokeClosure(a) => a,
            DerefPointer(a) => a,
            FreeVariable(a, _) => a,
            IndexSlice(a) => a,
            RelateObjectBound(a) => a,
            RelateParamBound(a, _) => a,
            RelateRegionParamBound(a) => a,
            RelateDefaultParamBound(a, _) => a,
            Reborrow(a) => a,
            ReborrowUpvar(a, _) => a,
            DataBorrowed(_, a) => a,
            ReferenceOutlivesReferent(_, a) => a,
            ParameterInScope(_, a) => a,
            ExprTypeIsNotInScope(_, a) => a,
            BindingTypeIsNotValidAtDecl(a) => a,
            CallRcvr(a) => a,
            CallArg(a) => a,
            CallReturn(a) => a,
            Operand(a) => a,
            AddrOf(a) => a,
            AutoBorrow(a) => a,
            SafeDestructor(a) => a,
        }
    }
}

impl RegionVariableOrigin {
    pub fn span(&self) -> Span {
        match *self {
            MiscVariable(a) => a,
            PatternRegion(a) => a,
            AddrOfRegion(a) => a,
            Autoref(a) => a,
            Coercion(a) => a,
            EarlyBoundRegion(a, _) => a,
            LateBoundRegion(a, _, _) => a,
            BoundRegionInCoherence(_) => codemap::DUMMY_SP,
            UpvarRegion(_, a) => a
        }
    }
}

// --------------------------------------------------------------

#[derive(Clone)]
pub struct FulfilledPredicates<'tcx> {
    set: FnvHashSet<(RFC1214Warning, ty::Predicate<'tcx>)>,
}


impl<'tcx> SnapshotVecDelegate for PredicateObligation<'tcx> {
    type Value = Self;
    type Undo = ();

    fn reverse(_values: &mut Vec<PredicateObligation<'tcx>>, _action: ()) {
        ()
    }
}

impl<'tcx> SnapshotVecDelegate for RegionObligation<'tcx> {
    type Value = Self;
    type Undo = ();

    fn reverse(_values: &mut Vec<RegionObligation<'tcx>>, _action: ()) {
        ()
    }
}

// In the new fulfillment context model of using a tree, we will preseve the
// entire proof tree for multiple reasons.
//
// In this case as we complete branches of work we will mark them as complete
// in order to prevent recursing down them redoing work.
//
// This allows the fulfillment context to only track least upper bound of
// all unfinished work in the tree. We can then only recurse down branches
// that have not yet been completed.
#[derive(Clone)]
pub struct PendingPredicateObligation<'tcx> {
    complete: bool,
    pub obligation: PredicateObligation<'tcx>
}

impl<'tcx> PendingPredicateObligation<'tcx> {
    pub fn new(obligation: PredicateObligation<'tcx>) -> PendingPredicateObligation<'tcx> {
        PendingPredicateObligation {
            complete: false,
            obligation: obligation
        }
    }

    pub fn complete(&mut self) {
        self.complete = true
    }

    pub fn is_complete(&self) -> bool {
        self.complete
    }
}

#[derive(Clone)]
pub struct RegionObligation<'tcx> {
    pub sub_region: ty::Region,
    pub sup_type: Ty<'tcx>,
    pub cause: ObligationCause<'tcx>,
}

impl<'tcx> FulfilledPredicates<'tcx> {
    pub fn new() -> FulfilledPredicates<'tcx> {
        FulfilledPredicates {
            set: FnvHashSet()
        }
    }

    pub fn is_duplicate(&self, w: RFC1214Warning, p: &ty::Predicate<'tcx>) -> bool {
        let key = (w, p.clone());
        self.set.contains(&key)
    }

    fn is_duplicate_or_add(&mut self, w: RFC1214Warning, p: &ty::Predicate<'tcx>) -> bool {
        let key = (w, p.clone());
        !self.set.insert(key)
    }
}

impl<'a, 'tcx> TransactionalMut for InferCtxt<'a, 'tcx> {
    type Snapshot = CombinedSnapshot<'tcx>;


    fn start_snapshot(&mut self) -> CombinedSnapshot<'tcx> {
        CombinedSnapshot {
            type_snapshot: self.type_variables.borrow_mut().snapshot(),
            int_snapshot: self.int_unification_table.borrow_mut().snapshot(),
            float_snapshot: self.float_unification_table.borrow_mut().snapshot(),
            region_vars_snapshot: self.region_vars.start_snapshot(),
            predicates_snapshot: self.predicates.snapshot(),
            region_obligations_snapshot: self.region_obligations
                                            .iter_mut()
                                            .map(|(k, v)| (*k, v.start_snapshot()))
                                            .collect(),
            duplicate_set: self.duplicate_set.clone(),
        }
    }

    fn rollback_to(&mut self, cause: &str, snapshot: CombinedSnapshot<'tcx>) {
        debug!("rollback_to(cause={})", cause);

        let CombinedSnapshot { type_snapshot,
                               int_snapshot,
                               float_snapshot,
                               region_vars_snapshot,
                               predicates_snapshot,
                               region_obligations_snapshot,
                               duplicate_set } = snapshot;

        self.type_variables
            .borrow_mut()
            .rollback_to(type_snapshot);

        self.int_unification_table
            .borrow_mut()
            .rollback_to(int_snapshot);

        self.float_unification_table
            .borrow_mut()
            .rollback_to(float_snapshot);

        self.region_vars
            .rollback_to(region_vars_snapshot);

        self.predicates.rollback_to(predicates_snapshot);

        for (k, v) in region_obligations_snapshot {
            self.region_obligations.get_mut(&k).unwrap().rollback_to(v);
        }

        self.duplicate_set = duplicate_set;
    }

    fn commit_from(&mut self, snapshot: CombinedSnapshot<'tcx>) {
        debug!("commit_from!");
        let CombinedSnapshot { type_snapshot,
                               int_snapshot,
                               float_snapshot,
                               region_vars_snapshot,
                               predicates_snapshot,
                               region_obligations_snapshot,
                               .. } = snapshot;

        self.type_variables
            .borrow_mut()
            .commit(type_snapshot);

        self.int_unification_table
            .borrow_mut()
            .commit(int_snapshot);

        self.float_unification_table
            .borrow_mut()
            .commit(float_snapshot);

        self.region_vars
            .commit(region_vars_snapshot);

        self.predicates.commit(predicates_snapshot);

        for (k, v) in region_obligations_snapshot {
            self.region_obligations.get_mut(&k).unwrap().commit(v);
        }

        // we implicitly commit the mutation to the duplicate_set here
    }
}
