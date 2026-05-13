import Ambifine.Untyped
import Ambifine.Context

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

def _root_.Hyp.wk1 : Hyp → Hyp
| .gst ty => .gst ty.wk1
| .type ty => .type ty.wk1
| .prop ty => .prop (ty.liftLooseBVars 0 1)

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

def Term.subst (e : Term) (s : Subst ) : Term :=
  match e with
  | Term.proof _ _ => e
  | Term.expr _ => e
  | Term.var n => s n
  | Term.const k => Term.const k
  | Term.unary k t => Term.unary k (t.subst s)
  | Term.bin k l r => Term.bin k (l.subst s) (r.subst s)
  | Term.abs k A t => Term.abs k (A.subst s) (t.subst s.lift)
  | Term.pabs k A t => Term.pabs k A (t.subst s.lift)
  | Term.tri k A l r => Term.tri k (A.subst s) (l.subst s) (r.subst s)
  | Term.ir k x y P => Term.ir k (x.subst s) (y.subst s) (P.subst s.lift)
  | Term.cases k K d l r =>
      Term.cases k (K.subst s) (d.subst s) (l.subst s.lift) (r.subst s.lift)
  | Term.let_bin k P e e' =>
      Term.let_bin k (P.subst s) (e.subst s) (e'.subst s.lift.lift)
  | Term.let_bin_beta k P l r e' =>
      Term.let_bin_beta k (P.subst s) (l.subst s) (r.subst s) (e'.subst s.lift.lift)
  | Term.nr k K e z q =>
      Term.nr k (K.subst s.lift) (e.subst s) (z.subst s) (q.subst s.lift.lift)
  | Term.nz k K z q =>
      Term.nz k (K.subst s.lift) (z.subst s) (q.subst s.lift.lift)
  | Term.lr k K e n c =>
      Term.lr k (K.subst s.lift) (e.subst s) (n.subst s) (c.subst s.lift.lift.lift)

-- Single-variable substitution: replace var 0 with t, decrement all others.
def Subst.subst0 (t : Term) : Subst
  | 0     => t
  | n + 1 => .var n

def Term.subst0 (e r : Term) : Term := e.subst (Subst.subst0 r)

-- alpha-substitution: replace var 0 with t, leave all other variables unchanged.
-- Unlike subst0, does NOT decrement vars ≥ 1.  Used for motive instantiation
-- in eliminator result types (natrec step, case branches, etc.).
def Subst.alpha0 (t : Term) : Subst
  | 0     => t
  | n + 1 => .var (n + 1)

def Term.alpha0 (e r : Term) : Term := e.subst (Subst.alpha0 r)

-- Abstract over variable k in t: lift t by 1, then replace var (k+1) with var 0.
-- Produces predicate P satisfying P.subst0(var k) = t.
def Term.abstractVar (k : Nat) (t : Term) : Term :=
  (t.lift 0 1).subst fun j => if j == k + 1 then .var 0 else .var j

end Untyped
