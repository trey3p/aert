import Ambifine.Surface
import Ambifine.Untyped
import Ambifine.UntypedToExpr
import Ambifine.Subst
import Lean
open Lean Meta Elab Command

private def buildNat : Nat → Untyped.Term
  | 0 => Untyped.Term.zero
  | k+1 => Untyped.Term.app Untyped.Term.nats Untyped.Term.succ (buildNat k)

mutual

partial def elabErtType (ctx : List (Name × Untyped.Term)) : Syntax → CommandElabM Untyped.Term
  | `(ertType| 𝟙) => return Untyped.Term.unit
  | `(ertType| ($x : $A) → $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType ((xName, A_term) :: ctx) B
    return Untyped.Term.pi A_term B_term
  | `(ertType| ($x : $A) × $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType ((xName, A_term) :: ctx) B
    return Untyped.Term.sigma A_term B_term
  | `(ertType| $A + $B) => do
    let A_term ← elabErtType ctx A
    let B_term ← elabErtType ctx B
    return Untyped.Term.coprod A_term B_term
  | `(ertType| ($x : $P) ⇒ $B) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let B_term ← elabErtType ((xName, P_term) :: ctx) B
    return Untyped.Term.assume P_term B_term
  | `(ertType| {$x : $A | $P}) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let P_term ← elabErtProp ((xName, A_term) :: ctx) P
    return Untyped.Term.set A_term P_term
  | `(ertType| ∀ $x : $A, $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType ((xName, A_term) :: ctx) B
    return Untyped.Term.intersect A_term B_term
  | `(ertType| ∃ $x : $A, $B) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let B_term ← elabErtType ((xName, A_term) :: ctx) B
    return Untyped.Term.union A_term B_term
  | `(ertType| ℕ) => return Untyped.Term.nats
  | `(ertType| ($A)) => elabErtType ctx A
  | stx => throwErrorAt stx "Unsupported ERT type: {stx}"

partial def elabErtProp (ctx : List (Name × Untyped.Term)) : Syntax → CommandElabM Untyped.Term
  | `(ertProp| ⊤) => return Untyped.Term.top
  | `(ertProp| ⊥) => return Untyped.Term.bot
  | `(ertProp| ($x : $P) ⇒ $Q) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let Q_term ← elabErtProp ((xName, P_term) :: ctx) Q
    return Untyped.Term.dimplies P_term Q_term
  | `(ertProp| ($x : $P) ∧ $Q) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let Q_term ← elabErtProp ((xName, P_term) :: ctx) Q
    return Untyped.Term.dand P_term Q_term
  | `(ertProp| $P ∨ $Q) => do
    let P_term ← elabErtProp ctx P
    let Q_term ← elabErtProp ctx Q
    return Untyped.Term.or P_term Q_term
  | `(ertProp| ∀ $x : $A, $P) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let P_term ← elabErtProp ((xName, A_term) :: ctx) P
    return Untyped.Term.forall_ A_term P_term
  | `(ertProp| ∃ $x : $A, $P) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let P_term ← elabErtProp ((xName, A_term) :: ctx) P
    return Untyped.Term.exists_ A_term P_term
  | `(ertProp| $t:ertTerm = $u:ertTerm) => do
    let t_term ← elabErtTerm ctx t
    let u_term ← elabErtTerm ctx u
    /- `eq` expects to have the type of the two terms,
      we leave a placeholder of unit for the type.
    -/
    return Untyped.Term.eq Untyped.Term.unit t_term u_term
  | `(ertProp| ($P)) => elabErtProp ctx P
  | stx => throwErrorAt stx "Unsupported ERT prop: {stx}"

partial def elabErtTerm (ctx : List (Name × Untyped.Term)) : Syntax → CommandElabM Untyped.Term
  | `(ertTerm| succ) => return Untyped.Term.succ
  | `(ertTerm| $x:ident) => do
    let xName := x.getId
    match ctx.findIdx? (·.fst == xName) with
    | some i => return Untyped.Term.var i
    | none => throwErrorAt x "Unknown variable: {xName}"
  | `(ertTerm| λ $x : $A:ertType . $t) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let t_term ← elabErtTerm ((xName, A_term) :: ctx) t
    return Untyped.Term.lam A_term t_term
  | `(ertTerm| λ $x : $P:ertProp . $t) => do
    let P_term ← elabErtProp ctx P
    let xName := x.getId
    let t_term ← elabErtTerm ((xName, P_term) :: ctx) t
    return Untyped.Term.lam_pr P_term t_term
  | `(ertTerm| $f:ertTerm $a:ertTerm) => do
    let f_term ← elabErtTerm ctx f
    let a_term ← elabErtTerm ctx a
    /- `app` expects the type of the function to be given
    - We leave a placeholder of `unit` there so that it can be inferred later. -/
    return Untyped.Term.app Untyped.Term.unit f_term a_term
  | `(ertTerm| $f:ertTerm ($a:term : $P:ertProp)) => do
    let f_term ← elabErtTerm ctx f
    let P_term ← elabErtProp ctx P
    let proof ← liftTermElabM $
      withCtxToLocalCtx ctx [] fun fvars => do
        let expectedType ← P_term.toExpr fvars
        Term.elabTermAndSynthesize a (some expectedType)
    /- `app_pr` expects the type of the function to be given
    - We leave a placeholder of `unit` there so that it can be inferred later. -/
    return Untyped.Term.app_pr Untyped.Term.unit f_term (Untyped.Term.proof proof P_term)
  | `(ertTerm| ($t, $u)) => do
    let t_term ← elabErtTerm ctx t
    let u_term ← elabErtTerm ctx u
    return Untyped.Term.pair t_term u_term
  | `(ertTerm| let ($x, $y) : $A = $e in $b) => do
    let A_term ← elabErtType ctx A
    let (x_term, y_term) ←
      match A_term with
      | Untyped.Term.sigma x_term y_term => pure (x_term, y_term)
      | _ => throwErrorAt A "invalid type in let-pair"
    let e_term ← elabErtTerm ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm ((yName, y_term) :: (xName, x_term) :: ctx) b
    return Untyped.Term.let_pair .type A_term e_term b_term
  | `(ertTerm| (inl $t) : $AB:ertType) => do
    return Untyped.Term.inj (0 : Fin 2) (← elabErtType ctx AB) (← elabErtTerm ctx t)
  | `(ertTerm| (inr $t) : $AB:ertType) => do
    return Untyped.Term.inj (1 : Fin 2) (← elabErtType ctx AB) (← elabErtTerm ctx t)
  | `(ertTerm| cases [$x : $D ↦ $C] $d |inl ($xl : $A) ↦ $l |inr ($xr : $B) ↦ $r) => do
    let xName := x.getId
    let D_term ← elabErtType ctx D
    let C_term ← elabErtType ((xName, D_term) :: ctx) C
    let K_term := Untyped.Term.lam D_term C_term
    let d_term ← elabErtTerm ctx d
    let A_term ← elabErtType ctx A
    let xlName := xl.getId
    let l_term ← elabErtTerm ((xlName, A_term) :: ctx) l
    let xrName := xr.getId
    let B_term ← elabErtType ctx B
    let r_term ← elabErtTerm ((xrName, B_term) :: ctx) r
    return Untyped.Term.case .type K_term d_term l_term r_term
  | `(ertTerm| {$x, $p : $P}) => do
    let x_term ← elabErtTerm ctx x
    let P_term ← elabErtProp ctx P
    let p_term ← liftTermElabM $ do
      withCtxToLocalCtx ctx [] fun fvars => do
      let expectedType ← P_term.toExpr fvars
      Term.elabTermAndSynthesize p (some expectedType)
    return Untyped.Term.elem x_term (Untyped.Term.proof p_term P_term)
  | `(ertTerm| let {$a, $b} : $A = $x in $e) => do
    let A_term ← elabErtType ctx A
    let (a_term, b_term) ←
      match A_term with
      | Untyped.Term.set a_term b_term => pure (a_term, b_term)
      | _ => throwErrorAt A "invalid type in let-set"
    let x_term ← elabErtTerm ctx x
    let aName := a.getId
    let bName := b.getId
    let e_term ← elabErtTerm ((bName, b_term) :: (aName, a_term) :: ctx) e
    return Untyped.Term.let_set .type A_term x_term e_term
  | `(ertTerm| λ ‖$x : $A‖ . $t) => do
    let A_term ← elabErtType ctx A
    let xName := x.getId
    let t_term ← elabErtTerm ((xName, A_term) :: ctx) t
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
    let (x_term, y_term) ←
      match A_term with
      | Untyped.Term.union x_term y_term => pure (x_term, y_term)
      | _ => throwErrorAt A "invalid type of let-repr"
    let e_term ← elabErtTerm ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm ((yName, y_term) :: (xName, x_term) :: ctx) b
    return Untyped.Term.let_repr .type A_term e_term b_term
  | `(ertTerm| $n:num) =>
    return buildNat n.getNat
  | `(ertTerm| natrec [$x ↦ $C:ertType] $e:ertTerm | $z:ertTerm
    | ‖succ $xs:ident‖ , $xp ↦ $s) => do
    let xName := x.getId
    -- K has 1 binder in nr [1,0,0,2]: elaborate body with x in scope directly
    let K_term ← elabErtType ((xName, Untyped.Term.nats) :: ctx) C
    let e_term ← elabErtTerm ctx e
    let z_term ← elabErtTerm ctx z
    let xsName := xs.getId
    let xpName := xp.getId
    let s_term ← elabErtTerm ((xpName, K_term) :: (xsName, Untyped.Term.nats) :: ctx) s
    return Untyped.Term.natrec .type K_term e_term z_term s_term
  | `(ertTerm| ($t)) => elabErtTerm ctx t
  | stx => throwErrorAt stx "Unsupported ERT term: {stx}"

end

def elabErtStatement : CommandElab
  | `(ertStatement| def $_name : $ty:ertType := $body) => do
    let _type ← elabErtType [] ty
    let _term ← elabErtTerm [] body
    -- Lean.logInfo m!"type: {repr type}\nterm: {repr term}"
  | `(ertStatement| def $_name : $prop:ertProp := $body) => do
    let prop ← elabErtProp [] prop
    let expectedType ← liftTermElabM $ prop.toExpr []
    let _body ← liftTermElabM $ Term.elabTermAndSynthesize body expectedType
  | _ => throwUnsupportedSyntax

@[command_elab ert]
def ertImpl : CommandElab := fun stx => do
  for i in stx[2].getArgs do
    elabErtStatement i
