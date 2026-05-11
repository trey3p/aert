import Ambifine.Check
import Ambifine.Infer
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

partial def elabErtType (env : List Statement)
    (ctx : NamedCtx) : Syntax → CommandElabM Untyped.Annot
  | `(ertType| 𝟙) => return .expr .type Untyped.Term.unit
  | `(ertType| ($x : $A) → $B) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let A_hyp : Hyp := ⟨A_term, .val .type⟩
    let xName := x.getId
    let .expr _ B_term ← elabErtType env ((xName, A_hyp) :: ctx) B | throwErrorAt B "expected type expression"
    return .expr .type (Untyped.Term.pi A_term B_term)
  | `(ertType| ($x : $A) × $B) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .expr _ B_term ← elabErtType env ((xName, Hyp.val A_term .type) :: ctx) B | throwErrorAt B "expected type expression"
    return .expr .type (Untyped.Term.sigma A_term B_term)
  | `(ertType| $A + $B) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let .expr _ B_term ← elabErtType env ctx B | throwErrorAt B "expected type expression"
    return .expr .type (Untyped.Term.coprod A_term B_term)
  | `(ertType| ($x : $P) ⇒ $B) => do
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let xName := x.getId
    let .expr _ B_term ← elabErtType env ((xName, Hyp.val P_term .prop) :: ctx) B | throwErrorAt B "expected type expression"
    return .expr .type (Untyped.Term.assume P_term B_term)
  | `(ertType| {$x : $A | $P}) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .expr _ P_term ← elabErtProp env ((xName, Hyp.val A_term .type) :: ctx) P | throwErrorAt P "expected prop expression"
    return .expr .type (Untyped.Term.set A_term P_term)
  | `(ertType| ∀ $x : $A, $B) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .expr _ B_term ← elabErtType env ((xName, Hyp.val A_term .type) :: ctx) B | throwErrorAt B "expected type expression"
    return .expr .type (Untyped.Term.intersect A_term B_term)
  | `(ertType| ∃ $x : $A, $B) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .expr _ B_term ← elabErtType env ((xName, Hyp.val A_term .type) :: ctx) B | throwErrorAt B "expected type expression"
    return .expr .type (Untyped.Term.union A_term B_term)
  | `(ertType| ℕ) => return .expr .type Untyped.Term.nats
  | `(ertType| ($A)) => elabErtType env ctx A
  | `(ertType| list $A) => do
    let .expr _ A_term ← elabErtType env ctx A
      | throwErrorAt A "expected type expression"
    return .expr .type (Untyped.Term.list A_term)
  | stx => throwErrorAt stx "Unsupported ERT type: {stx}"

partial def elabErtProp (env : List Statement)
    (ctx : NamedCtx) : Syntax → CommandElabM Untyped.Annot
  | `(ertProp| ⊤) => return .expr .prop Untyped.Term.top
  | `(ertProp| ⊥) => return .expr .prop Untyped.Term.bot
  | `(ertProp| ($x : $P) ⇒ $Q) => do
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let xName := x.getId
    let .expr _ Q_term ← elabErtProp env ((xName, Hyp.val P_term .prop) :: ctx) Q | throwErrorAt Q "expected prop expression"
    return .expr .prop (Untyped.Term.dimplies P_term Q_term)
  | `(ertProp| ($x : $P) ∧ $Q) => do
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let xName := x.getId
    let .expr _ Q_term ← elabErtProp env ((xName, Hyp.val P_term .prop) :: ctx) Q | throwErrorAt Q "expected prop expression"
    return .expr .prop (Untyped.Term.dand P_term Q_term)
  | `(ertProp| $P ∨ $Q) => do
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let .expr _ Q_term ← elabErtProp env ctx Q | throwErrorAt Q "expected prop expression"
    return .expr .prop (Untyped.Term.or P_term Q_term)
  | `(ertProp| ∀ $x : $A, $P) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .expr _ P_term ← elabErtProp env ((xName, Hyp.val A_term .type) :: ctx) P | throwErrorAt P "expected prop expression"
    return .expr .prop (Untyped.Term.forall_ A_term P_term)
  | `(ertProp| ∃ $x : $A, $P) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .expr _ P_term ← elabErtProp env ((xName, Hyp.val A_term .type) :: ctx) P | throwErrorAt P "expected prop expression"
    return .expr .prop (Untyped.Term.exists_ A_term P_term)
  | `(ertProp| $t:ertTerm =($A:ertType) $u:ertTerm) => do
    let t_term ← elabErtTerm env ctx t
    let u_term ← elabErtTerm env ctx u
    let .expr _ A_term ← elabErtType env ctx A
      | throwErrorAt A m!"Expected type, got {repr A}"
    return .expr .prop (Untyped.Term.eq A_term t_term u_term)
  | `(ertProp| ($P)) => elabErtProp env ctx P
  | stx => throwErrorAt stx "Unsupported ERT prop: {stx}"

partial def elabErtTerm (env : List Statement) (ctx : NamedCtx) : Syntax → CommandElabM Untyped.Term
  | `(ertTerm| succ) => return Untyped.Term.succ
  | `(ertTerm| $x:ident) => do
    let xName := x.getId
    match ctx.findIdx? (·.fst == xName) with
    | some i => return Untyped.Term.var i
    | none =>
      if env.map (·.name) |>.contains xName then
        return Untyped.Term.const (Untyped.TermKind.definition xName)
      else
        throwErrorAt x "Unknown variable: {xName}"
  | `(ertTerm| λ $x : $A:ertType . $t) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let t_term ← elabErtTerm env ((xName, Hyp.val A_term .type) :: ctx) t
    return Untyped.Term.lam A_term t_term
  | `(ertTerm| λ $x : $P:ertProp . $t) => do
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let xName := x.getId
    let t_term ← elabErtTerm env ((xName, Hyp.val P_term .prop) :: ctx) t
    return Untyped.Term.lam_pr P_term t_term
  | `(ertTerm| ($f:ertTerm : $A:ertType) $a:ertTerm) => do
    let f_term ← elabErtTerm env ctx f
    let a_term ← elabErtTerm env ctx a
    let .expr _ A_term ← elabErtType env ctx A
      | throwErrorAt A m!"Expected type, got {repr A}"
    return Untyped.Term.app A_term f_term a_term
  | `(ertTerm| $f:ertTerm ($a:term : $P:ertProp)) => do
    let f_term ← elabErtTerm env ctx f
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let proof ← liftTermElabM $
      withCtxToLocalCtx env ctx [] fun fvars => do
        let expectedType ← P_term.toExpr env fvars
        Term.elabTermAndSynthesize a (some expectedType)
    /- `app_pr` expects the type of the function to be given
    - We leave a placeholder of `unit` there so that it can be inferred later. -/
    return Untyped.Term.app_pr Untyped.Term.unit f_term (Untyped.Term.proof proof P_term)
  | `(ertTerm| ($t, $u)) => do
    let t_term ← elabErtTerm env ctx t
    let u_term ← elabErtTerm env ctx u
    return Untyped.Term.pair t_term u_term
  | `(ertTerm| let ($x, $y) : $A = $e in $b) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let (x_term, y_term) ←
      match A_term with
      | Untyped.Term.sigma x_term y_term => pure (x_term, y_term)
      | _ => throwErrorAt A "invalid type in let-pair"
    let e_term ← elabErtTerm env ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm env ((yName, Hyp.val y_term .type) :: (xName, Hyp.val x_term .type) :: ctx) b
    return Untyped.Term.let_pair .type A_term e_term b_term
  | `(ertTerm| (inl $t) : $AB:ertType) => do
    let .expr _ AB_term ← elabErtType env ctx AB | throwErrorAt AB "expected type expression"
    return Untyped.Term.inj (0 : Fin 2) AB_term (← elabErtTerm env ctx t)
  | `(ertTerm| (inr $t) : $AB:ertType) => do
    let .expr _ AB_term ← elabErtType env ctx AB | throwErrorAt AB "expected type expression"
    return Untyped.Term.inj (1 : Fin 2) AB_term (← elabErtTerm env ctx t)
  | `(ertTerm| cases [$x : $D ↦ $C] $d |inl ($xl : $A) ↦ $l |inr ($xr : $B) ↦ $r) => do
    let xName := x.getId
    let .expr _ D_term ← elabErtType env ctx D | throwErrorAt D "expected type expression"
    let .expr _ C_term ← elabErtType env ((xName, Hyp.val D_term .type) :: ctx) C | throwErrorAt C "expected type expression"
    let K_term := Untyped.Term.lam D_term C_term
    let d_term ← elabErtTerm env ctx d
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xlName := xl.getId
    let l_term ← elabErtTerm env ((xlName, Hyp.val A_term .type) :: ctx) l
    let xrName := xr.getId
    let .expr _ B_term ← elabErtType env ctx B | throwErrorAt B "expected type expression"
    let r_term ← elabErtTerm env ((xrName, Hyp.val B_term .type) :: ctx) r
    return Untyped.Term.case .type K_term d_term l_term r_term
  | `(ertTerm| {$x, $p : $P} : $T) => do
    let x_term ← elabErtTerm env ctx x
    let .expr _ P_term ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let p_term ← liftTermElabM $ do
      withCtxToLocalCtx env ctx [] fun fvars => do
      let expectedType ← P_term.toExpr env fvars
      let proof ← Term.elabTermAndSynthesize p (some expectedType)
      mkLambdaFVars fvars.toArray proof
    let .expr _ T_term ← elabErtType env ctx T | throwErrorAt T "expected expression"
    return Untyped.Term.elem x_term (Untyped.Term.proof p_term P_term) T_term
  | `(ertTerm| let {$a, $b} : $A = $x in $e) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let (a_term, b_term) ←
      match A_term with
      | Untyped.Term.set a_term b_term => pure (a_term, b_term)
      | _ => throwErrorAt A "invalid type in let-set"
    let x_term ← elabErtTerm env ctx x
    let aName := a.getId
    let bName := b.getId
    let e_term ← elabErtTerm env ((bName, Hyp.val b_term .prop) :: (aName, Hyp.val a_term .type) :: ctx) e
    return Untyped.Term.let_set .type A_term x_term e_term
  | `(ertTerm| λ ‖$x : $A‖ . $t) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let t_term ← elabErtTerm env ((xName, Hyp.val A_term .type) :: ctx) t
    return Untyped.Term.lam_irrel A_term t_term
  | `(ertTerm| $f:ertTerm (‖ $a:ertTerm ‖) ) => do
    let f_term ← elabErtTerm env ctx f
    let a_term ← elabErtTerm env ctx a
    return Untyped.Term.app_irrel Untyped.Term.unit f_term a_term
  | `(ertTerm| ( ‖$t‖, $u)) => do
    let t_term ← elabErtTerm env ctx t
    let u_term ← elabErtTerm env ctx u
    return Untyped.Term.repr t_term u_term
  | `(ertTerm| let ( ‖$x‖, $y) : $A = $e:ertTerm in $b) => do
    let .expr _ A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let (x_term, y_term) ←
      match A_term with
      | Untyped.Term.union x_term y_term => pure (x_term, y_term)
      | _ => throwErrorAt A "invalid type of let-repr"
    let e_term ← elabErtTerm env ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm env ((yName, Hyp.val y_term .type) :: (xName, Hyp.val x_term .type) :: ctx) b
    return Untyped.Term.let_repr .type A_term e_term b_term
  | `(ertTerm| $n:num) =>
    return buildNat n.getNat
  | `(ertTerm| natrec [$x ↦ $C:ertType] $e:ertTerm | $z:ertTerm
    | ‖succ $xs:ident‖ , $xp ↦ $s) => do
    let xName := x.getId
    -- K has 1 binder in nr [1,0,0,2]: elaborate body with x in scope directly
    let .expr _ K_term ← elabErtType env ((xName, Hyp.val Untyped.Term.nats .type) :: ctx) C | throwErrorAt C "expected type expression"
    let e_term ← elabErtTerm env ctx e
    let z_term ← elabErtTerm env ctx z
    let xsName := xs.getId
    let xpName := xp.getId
    let s_term ← elabErtTerm env ((xpName, Hyp.val K_term .type) :: (xsName, Hyp.val Untyped.Term.nats .type) :: ctx) s
    return Untyped.Term.natrec .type K_term e_term z_term s_term
  | `(ertTerm| ($t)) => elabErtTerm env ctx t
  | `(ertTerm| nil : $A) => do
    let .expr _ A_term ← elabErtType env ctx A
      | throwErrorAt A "expected type expression"
    return Untyped.Term.em A_term
  | `(ertTerm| ($x : $A) :: $xs) => do
    let x_term ← elabErtTerm env ctx x
    let xs_term ← elabErtTerm env ctx xs
    let .expr _ A_term ← elabErtType env ctx A
      | throwErrorAt A "expected type expression"
    return Untyped.Term.cons A_term x_term xs_term
  | stx => throwErrorAt stx "Unsupported ERT term: {stx}"

end

def elabErtStatement (env : List Statement) : Syntax → CommandElabM Statement
  | `(ertStatement| def $name : $ty:ertType := $body) => do
    let annot@(.expr _ type) ← elabErtType env [] ty | throwErrorAt ty "expected a type"
    let term ← elabErtTerm env [] body
    try
      liftTermElabM $ Check.check env term annot
      return .defn name.getId type term
    catch msg =>
      throwErrorAt name msg.toMessageData
    -- Lean.logInfo m!"type: {repr type}\nterm: {repr term}"
  | `(ertStatement| def $name : $prop:ertProp := $body) => do
    let .expr _ prop ← elabErtProp env [] prop | throwErrorAt prop "expected prop expression"
    let expectedType ← liftTermElabM $ prop.toExpr env []
    let body ← liftTermElabM $ Term.elabTermAndSynthesize body expectedType
    if ← liftTermElabM $ isDefEq expectedType (← liftTermElabM $ inferType body) then
      return .thm name.getId prop body
    else
      throwErrorAt name "invalid proof"
  | _ => throwUnsupportedSyntax

@[command_elab ert]
def ertImpl : CommandElab := fun stx => do
  let mut env : List Statement := []
  for i in stx[2].getArgs do
    env := (← elabErtStatement env i) :: env
