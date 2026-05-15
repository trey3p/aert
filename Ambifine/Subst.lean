import Ambifine.Untyped
import Ambifine.Context
import Ambifine.UntypedToExpr

open Lean Meta

namespace Untyped

-- Shift all free variables with index ≥ cutoff up by shift.
-- The binding depth encoded in each TermKind index determines how much
-- the cutoff grows as lift descends under binders.
def Term.lift (cutoff shift : Nat) : Term → Term
  | .proof p Ty        => .proof (p.liftLooseBVars cutoff shift)
                                  (Ty.liftLooseBVars cutoff shift)
  | .expr e            => .expr (e.liftLooseBVars cutoff shift)
  | .var v             => .var (if v < cutoff then v else v + shift)
  | .const c           => .const c
  | .unary k t         => .unary k (t.lift cutoff shift)
  | .bin k l r         => .bin k (l.lift cutoff shift) (r.lift cutoff shift)
  | .abs k A t         => .abs k (A.lift cutoff shift) (t.lift (cutoff + 1) shift)
  | .pabs k A t        => .pabs k (A.liftLooseBVars cutoff shift)
                                   (t.lift (cutoff + 1) shift)
  | .tri k A l r       => .tri k (A.lift cutoff shift) (l.lift cutoff shift)
                                  (r.lift cutoff shift)
  | .ir k x y P        => .ir k (x.lift cutoff shift) (y.lift cutoff shift)
                                  (P.lift (cutoff + 1) shift)
  | .cases k K d l r   => .cases k (K.lift cutoff shift) (d.lift cutoff shift)
                                    (l.lift (cutoff + 1) shift)
                                    (r.lift (cutoff + 1) shift)
  | .let_bin k P e e'  => .let_bin k (P.lift cutoff shift) (e.lift cutoff shift)
                                      (e'.lift (cutoff + 2) shift)
  | .let_bin_beta k P l r e' =>
      .let_bin_beta k (P.lift cutoff shift) (l.lift cutoff shift)
                      (r.lift cutoff shift) (e'.lift (cutoff + 2) shift)
  | .nr k K e z s      => .nr k (K.lift (cutoff + 1) shift) (e.lift cutoff shift)
                                 (z.lift cutoff shift) (s.lift (cutoff + 2) shift)
  | .nz k K z s        => .nz k (K.lift (cutoff + 1) shift) (z.lift cutoff shift)
                                  (s.lift (cutoff + 2) shift)
  | .lr k K e n c      => .lr k (K.lift (cutoff + 1) shift) (e.lift cutoff shift)
                                  (n.lift cutoff shift) (c.lift (cutoff + 3) shift)

def Term.wk1 (t : Term) : Term := t.lift 0 1
def Term.wkn (n : Nat) (t : Term) : Term := t.lift 0 n

-- Custom Expr lowerer: Lean's `lowerLooseBVars e s d` returns `e` unchanged
-- when `s < d` (defensive guard).  We need to shift bvars `≥ cutoff` down
-- regardless, asserting the caller has verified no bvars in `[cutoff, cutoff+shift)`
-- are referenced.
partial def _root_.Lean.Expr.lowerLooseBVarsUnsafe (e : Lean.Expr) (cutoff shift : Nat) : Lean.Expr :=
  match e with
  | .bvar n => if n < cutoff then .bvar n else .bvar (n - shift)
  | .app f a => .app (f.lowerLooseBVarsUnsafe cutoff shift) (a.lowerLooseBVarsUnsafe cutoff shift)
  | .lam n t b bi =>
      .lam n (t.lowerLooseBVarsUnsafe cutoff shift) (b.lowerLooseBVarsUnsafe (cutoff + 1) shift) bi
  | .forallE n t b bi =>
      .forallE n (t.lowerLooseBVarsUnsafe cutoff shift) (b.lowerLooseBVarsUnsafe (cutoff + 1) shift) bi
  | .letE n t v b nd =>
      .letE n (t.lowerLooseBVarsUnsafe cutoff shift) (v.lowerLooseBVarsUnsafe cutoff shift)
              (b.lowerLooseBVarsUnsafe (cutoff + 1) shift) nd
  | .mdata m e' => .mdata m (e'.lowerLooseBVarsUnsafe cutoff shift)
  | .proj n i e' => .proj n i (e'.lowerLooseBVarsUnsafe cutoff shift)
  | e => e  -- const, fvar, mvar, sort, lit

-- Mirror of `Term.lift` that lowers free variables: bvars with index ≥ cutoff
-- are shifted down by `shift`.  Used to bring a body's type back into the
-- outer Γ when `let_set` returns it (the body was inferred under 2 extra
-- destructure binders).  Assumes none of the eliminated indices are referenced
-- — i.e., the term is well-formed in the smaller context.
def Term.liftDown (cutoff shift : Nat) : Term → Term
  | .proof p Ty        => .proof (p.lowerLooseBVarsUnsafe cutoff shift)
                                  (Ty.lowerLooseBVarsUnsafe cutoff shift)
  | .expr e            => .expr (e.lowerLooseBVarsUnsafe cutoff shift)
  | .var v             => .var (if v < cutoff then v else v - shift)
  | .const c           => .const c
  | .unary k t         => .unary k (t.liftDown cutoff shift)
  | .bin k l r         => .bin k (l.liftDown cutoff shift) (r.liftDown cutoff shift)
  | .abs k A t         => .abs k (A.liftDown cutoff shift) (t.liftDown (cutoff + 1) shift)
  | .pabs k A t        => .pabs k (A.lowerLooseBVars cutoff shift)
                                   (t.liftDown (cutoff + 1) shift)
  | .tri k A l r       => .tri k (A.liftDown cutoff shift) (l.liftDown cutoff shift)
                                  (r.liftDown cutoff shift)
  | .ir k x y P        => .ir k (x.liftDown cutoff shift) (y.liftDown cutoff shift)
                                  (P.liftDown (cutoff + 1) shift)
  | .cases k K d l r   => .cases k (K.liftDown cutoff shift) (d.liftDown cutoff shift)
                                    (l.liftDown (cutoff + 1) shift)
                                    (r.liftDown (cutoff + 1) shift)
  | .let_bin k P e e'  => .let_bin k (P.liftDown cutoff shift) (e.liftDown cutoff shift)
                                      (e'.liftDown (cutoff + 2) shift)
  | .let_bin_beta k P l r e' =>
      .let_bin_beta k (P.liftDown cutoff shift) (l.liftDown cutoff shift)
                      (r.liftDown cutoff shift) (e'.liftDown (cutoff + 2) shift)
  | .nr k K e z s      => .nr k (K.liftDown (cutoff + 1) shift) (e.liftDown cutoff shift)
                                 (z.liftDown cutoff shift) (s.liftDown (cutoff + 2) shift)
  | .nz k K z s        => .nz k (K.liftDown (cutoff + 1) shift) (z.liftDown cutoff shift)
                                  (s.liftDown (cutoff + 2) shift)
  | .lr k K e n c      => .lr k (K.liftDown (cutoff + 1) shift) (e.liftDown cutoff shift)
                                  (n.liftDown cutoff shift) (c.liftDown (cutoff + 3) shift)

def _root_.Hyp.wk1 : Hyp → Hyp
| .gst ty => .gst ty.wk1
| .type ty => .type ty.wk1
| .prop ty => .prop (ty.liftLooseBVars 0 1)
| .destructVal ty src => .destructVal ty.wk1 src.wk1
| .destructProp ty src => .destructProp (ty.liftLooseBVars 0 1) src.wk1

-- Computable analogue of HasVar: walk the context, applying wk1 at each step
-- so the returned type is valid in the full context (not just the tail).
def lookupVar : Ctx → Nat → Option Hyp
  | [],     _     => none
  | h :: _, 0     => some h.wk1
  | _ :: Γ, n + 1 => lookupVar Γ n |>.map (fun h => h.wk1)

def Subst := Nat → Term

def Subst.lift (s : Subst) : Subst
  | 0 => Term.var 0
  | n + 1 => Term.wk1 (s n)

/-- Build the prefix of a `Subst` as an `Array Expr`, suitable for
    `Expr.instantiate` against a payload whose loose-bvar range is `n`. -/
private def Subst.toExprArr (s : Subst) (n : Nat) : MetaM (Array Expr) :=
  (List.range n).toArray.mapM (fun i => (s i).toExprBVars)

partial def Term.subst (e : Term) (s : Subst) : MetaM Term := do
  match e with
  | Term.proof p Ty =>
    let pArr ← s.toExprArr p.looseBVarRange
    let tArr ← s.toExprArr Ty.looseBVarRange
    return Term.proof (p.instantiate pArr) (Ty.instantiate tArr)
  | Term.expr e' =>
    let arr ← s.toExprArr e'.looseBVarRange
    return Term.expr (e'.instantiate arr)
  | Term.var n => return s n
  | Term.const k => return Term.const k
  | Term.unary k t => return Term.unary k (← t.subst s)
  | Term.bin k l r => return Term.bin k (← l.subst s) (← r.subst s)
  | Term.abs k A t => return Term.abs k (← A.subst s) (← t.subst s.lift)
  | Term.pabs k A t =>
    let arr ← s.toExprArr A.looseBVarRange
    return Term.pabs k (A.instantiate arr) (← t.subst s.lift)
  | Term.tri k A l r => return Term.tri k (← A.subst s) (← l.subst s) (← r.subst s)
  | Term.ir k x y P => return Term.ir k (← x.subst s) (← y.subst s) (← P.subst s.lift)
  | Term.cases k K d l r =>
      return Term.cases k (← K.subst s) (← d.subst s) (← l.subst s.lift) (← r.subst s.lift)
  | Term.let_bin k P e e' =>
      return Term.let_bin k (← P.subst s) (← e.subst s) (← e'.subst s.lift.lift)
  | Term.let_bin_beta k P l r e' =>
      return Term.let_bin_beta k (← P.subst s) (← l.subst s) (← r.subst s) (← e'.subst s.lift.lift)
  | Term.nr k K e z q =>
      return Term.nr k (← K.subst s.lift) (← e.subst s) (← z.subst s) (← q.subst s.lift.lift)
  | Term.nz k K z q =>
      return Term.nz k (← K.subst s.lift) (← z.subst s) (← q.subst s.lift.lift)
  | Term.lr k K e n c =>
      return Term.lr k (← K.subst s.lift) (← e.subst s) (← n.subst s) (← c.subst s.lift.lift.lift)

-- Single-variable substitution: replace var 0 with t, decrement all others.
def Subst.subst0 (t : Term) : Subst
  | 0     => t
  | n + 1 => .var n

def Term.subst0 (e r : Term) : MetaM Term := e.subst (Subst.subst0 r)

-- alpha-substitution: replace var 0 with t, leave all other variables unchanged.
-- Unlike subst0, does NOT decrement vars ≥ 1.  Used for motive instantiation
-- in eliminator result types (natrec step, case branches, etc.).
def Subst.alpha0 (t : Term) : Subst
  | 0     => t
  | n + 1 => .var (n + 1)

def Term.alpha0 (e r : Term) : MetaM Term := e.subst (Subst.alpha0 r)

-- Abstract over variable k in t: lift t by 1, then replace var (k+1) with var 0.
-- Produces predicate P satisfying P.subst0(var k) = t.
def Term.abstractVar (k : Nat) (t : Term) : MetaM Term :=
  (t.lift 0 1).subst fun j => if j == k + 1 then .var 0 else .var j

end Untyped
