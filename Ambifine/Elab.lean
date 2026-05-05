import Ambifine.Surface
import Ambifine.Untyped
import Lean
open Lean Meta Elab Command

private def buildNat : Nat → Untyped.Term
  | 0 => Untyped.Term.zero
  | k+1 => Untyped.Term.app Untyped.Term.nats Untyped.Term.succ (buildNat k)

mutual

partial def elabErtType (ctx : List Name) : Syntax → CommandElabM Untyped.Term
  | `(ertType| 𝟙) => return Untyped.Term.unit
  | `(ertType| ($x : $A) → $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType (xName :: ctx) B
    return Untyped.Term.pi A_term B_term
  | `(ertType| ($x : $A) × $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType (xName :: ctx) B
    return Untyped.Term.sigma A_term B_term
  | `(ertType| $A + $B) => do
    let A_term ← elabErtType ctx A
    let B_term ← elabErtType ctx B
    return Untyped.Term.coprod A_term B_term
  | `(ertType| ($x : $P) ⇒ $B) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let B_term ← elabErtType (xName :: ctx) B
    return Untyped.Term.assume P_term B_term
  | `(ertType| {$x : $A | $P}) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let P_term ← elabErtProp (xName :: ctx) P
    return Untyped.Term.set A_term P_term
  | `(ertType| ∀ $x : $A, $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType (xName :: ctx) B
    return Untyped.Term.intersect A_term B_term
  | `(ertType| ∃ $x : $A, $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType (xName :: ctx) B
    return Untyped.Term.union A_term B_term
  | `(ertType| ℕ) => return Untyped.Term.nats
  | `(ertType| ($A)) => elabErtType ctx A
  | stx => throwErrorAt stx "Unsupported ERT type: {stx}"

partial def elabErtProp (ctx : List Name) : Syntax → CommandElabM Untyped.Term
  | `(ertProp| ⊥) => return Untyped.Term.bot
  | `(ertProp| ($x : $P) ⇒ $Q) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let Q_term ← elabErtProp (xName :: ctx) Q
    return Untyped.Term.dimplies P_term Q_term
  | `(ertProp| ($x : $P) ∧ $Q) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let Q_term ← elabErtProp (xName :: ctx) Q
    return Untyped.Term.dand P_term Q_term
  | `(ertProp| $P ∨ $Q) => do
    let P_term ← elabErtProp ctx P
    let Q_term ← elabErtProp ctx Q
    return Untyped.Term.or P_term Q_term
  | `(ertProp| ∀ $x : $A, $P) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let P_term ← elabErtProp (xName :: ctx) P
    return Untyped.Term.forall_ A_term P_term
  | `(ertProp| ∃ $x : $A, $P) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let P_term ← elabErtProp (xName :: ctx) P
    return Untyped.Term.exists_ A_term P_term
  | `(ertProp| $t:ertTerm = $u:ertTerm) => throwErrorAt t "Term elaboration not yet implemented"
  | `(ertProp| ($P)) => elabErtProp ctx P
  | stx => throwErrorAt stx "Unsupported ERT prop: {stx}"

end

partial def elabErtTerm (ctx : List Name) : Syntax → CommandElabM Untyped.Term
  | `(ertTerm| succ) => return Untyped.Term.succ
  | `(ertTerm| $x:ident) => do
    let xName := x.getId
    match ctx.findIdx? (· == xName) with
    | some i => return Untyped.Term.var i
    | none => throwErrorAt x "Unknown variable: {xName}"
  | `(ertTerm| λ $x : $A . $t) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let t_term ← elabErtTerm (xName :: ctx) t
    return Untyped.Term.lam A_term t_term
  | `(ertTerm| $f $a) => do
    let f_term ← elabErtTerm ctx f
    let a_term ← elabErtTerm ctx a
    /- `app` expects the type of the function to be given
    - We leave a placeholder of `unit` there so that it can be inferred later. -/
    return Untyped.Term.app Untyped.Term.unit f_term a_term
  | `(ertTerm| ($t, $u)) => do
    let t_term ← elabErtTerm ctx t
    let u_term ← elabErtTerm ctx u
    return Untyped.Term.pair t_term u_term
  | `(ertTerm| let ($x, $y) : $A = $e in $b) => do
    let A_term ← elabErtType ctx A
    let e_term ← elabErtTerm ctx e
    let xName := x.getId
    let yName := y.getId
    -- y is the inner binder (index 0), x is outer (index 1)
    let b_term ← elabErtTerm (yName :: xName :: ctx) b
    return Untyped.Term.let_pair .type A_term e_term b_term
  | `(ertTerm| inl $t) =>
    return Untyped.Term.inj (0 : Fin 2) (← elabErtTerm ctx t)
  | `(ertTerm| inr $t) =>
    return Untyped.Term.inj (1 : Fin 2) (← elabErtTerm ctx t)
  | `(ertTerm| cases [$x : $D ↦ $C] $d |inl $xl ↦ $l |inr $xr ↦ $r) => do
    let xName := x.getId
    let C_term ← elabErtType (xName :: ctx) C
    let D_term ← elabErtType ctx D
    let K_term := Untyped.Term.lam D_term C_term
    let d_term ← elabErtTerm ctx d
    let xlName := xl.getId
    let l_term ← elabErtTerm (xlName :: ctx) l
    let xrName := xr.getId
    let r_term ← elabErtTerm (xrName :: ctx) r
    return Untyped.Term.case .type K_term d_term l_term r_term
  | `(ertTerm| λ ‖$x : $A‖ . $t) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let t_term ← elabErtTerm (xName :: ctx) t
    return Untyped.Term.lam_irrel A_term t_term
  | `(ertTerm| $f:ertTerm (‖ $a:ertTerm ‖) ) => do
    let f_term ← elabErtTerm ctx f
    let a_term ← elabErtTerm ctx a
    return Untyped.Term.app_irrel Untyped.Term.unit f_term a_term
  | `(ertTerm| ( ‖$t‖, $u)) => do
    let t_term ← elabErtTerm ctx t
    let u_term ← elabErtTerm ctx u
    return Untyped.Term.repr t_term u_term
  | `(ertTerm| let ( ‖$x‖, $y) : $A = $e:ertTerm in $b) => do
    let A_term ← elabErtType ctx A
    let e_term ← elabErtTerm ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm (yName :: xName :: ctx) b
    return Untyped.Term.let_repr .type A_term e_term b_term
  | `(ertTerm| $n:num) =>
    return buildNat n.getNat
  | `(ertTerm| natrec [$x ↦ $C:ertType] $e:ertTerm | $z:ertTerm
    | ‖succ $xs:ident‖ , $xp ↦ $s) => do
    let xName := x.getId
    -- K has 1 binder in nr [1,0,0,2]: elaborate body with x in scope directly
    let K_term ← elabErtType (xName :: ctx) C
    let e_term ← elabErtTerm ctx e
    let z_term ← elabErtTerm ctx z
    let xsName := xs.getId
    let xpName := xp.getId
    -- xp is the inner binder (IH, index 0), xs is outer (predecessor, index 1)
    let s_term ← elabErtTerm (xpName :: xsName :: ctx) s
    return Untyped.Term.natrec .type K_term e_term z_term s_term
  | `(ertTerm| ($t)) => elabErtTerm ctx t
  | stx => throwErrorAt stx "Unsupported ERT term: {stx}"

def elabErtStatement : CommandElab
  | `(ertStatement| def $name : $ty := $body) => do
    let type ← elabErtType [] ty
    let term ← elabErtTerm [] body
    Lean.logInfo m!"type: {repr type}\nterm: {repr term}"
  | _ => throwUnsupportedSyntax

@[command_elab ert]
def ertImpl : CommandElab := fun stx => do
  for i in stx[2].getArgs do
    elabErtStatement i

set_option pp.rawOnError true
#lang ERT
def test : (x : 𝟙) → 𝟙 := 3
def test2 : 𝟙 := 5
