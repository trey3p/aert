import Ambifine.Check
import Ambifine.Infer
import Ambifine.Surface
import Ambifine.Untyped
import Ambifine.UntypedToExpr
import Ambifine.Subst
import Lean
import Qq
open Lean Meta Elab Command
open Qq

private def buildNat : Nat → Untyped.Term
  | 0 => Untyped.Term.zero
  | k+1 => Untyped.Term.app Untyped.Term.nats Untyped.Term.succ (buildNat k)

mutual

partial def elabErtType (env : List Statement)
    (ctx : NamedCtx) : Syntax → CommandElabM Untyped.Annot
  | `(ertType| 𝟙) => return .exprType Untyped.Term.unit
  | `(ertType| ($x : $A) → $B) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .exprType B_term ← elabErtType env ((xName, Hyp.type A_term) :: ctx) B
      | throwErrorAt B "expected type expression"
    return .exprType (Untyped.Term.pi A_term B_term)
  | `(ertType| ($x : $A) × $B) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .exprType B_term ← elabErtType env ((xName, Hyp.type A_term) :: ctx) B
      | throwErrorAt B "expected type expression"
    return .exprType (Untyped.Term.sigma A_term B_term)
  | `(ertType| $A + $B) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let .exprType B_term ← elabErtType env ctx B | throwErrorAt B "expected type expression"
    return .exprType (Untyped.Term.coprod A_term B_term)
  | `(ertType| ($x : $P) ⇒ $B) => do
    let .exprProp P_expr ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let xName := x.getId
    let .exprType B_term ← elabErtType env ((xName, Hyp.prop P_expr) :: ctx) B
      | throwErrorAt B "expected type expression"
    return .exprType (Untyped.Term.assume P_expr B_term)
  | `(ertType| {$x : $A | $P}) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .exprProp P_expr ← elabErtProp env ((xName, Hyp.type A_term) :: ctx) P
      | throwErrorAt P "expected prop expression"
    return .exprType (Untyped.Term.set A_term (Untyped.Term.expr P_expr))
  | `(ertType| ∀ $x : $A, $B) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .exprType B_term ← elabErtType env ((xName, Hyp.type A_term) :: ctx) B
      | throwErrorAt B "expected type expression"
    return .exprType (Untyped.Term.intersect A_term B_term)
  | `(ertType| ∃ $x : $A, $B) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let .exprType B_term ← elabErtType env ((xName, Hyp.type A_term) :: ctx) B
      | throwErrorAt B "expected type expression"
    return .exprType (Untyped.Term.union A_term B_term)
  | `(ertType| ℕ) => return .exprType Untyped.Term.nats
  | `(ertType| ($A)) => elabErtType env ctx A
  | `(ertType| list $A) => do
    let .exprType A_term ← elabErtType env ctx A
      | throwErrorAt A "expected type expression"
    return .exprType (Untyped.Term.list A_term)
  | stx => throwErrorAt stx "Unsupported ERT type: {stx}"

partial def elabErtProp (env : List Statement)
    (ctx : NamedCtx) (stx : Syntax) : CommandElabM Untyped.Annot := do
  let prop ← liftTermElabM $
    withCtxToLocalCtx env ctx [] fun fvars => do
      let prop ← Term.elabTermAndSynthesize stx (some q(Prop))
      return prop.abstract fvars.toArray.reverse
  return .exprProp prop

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
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let t_term ← elabErtTerm env ((xName, Hyp.type A_term) :: ctx) t
    return Untyped.Term.lam A_term t_term
  | `(ertTerm| ($f:ertTerm : $A:ertType) $a:ertTerm) => do
    let f_term ← elabErtTerm env ctx f
    let a_term ← elabErtTerm env ctx a
    let .exprType A_term ← elabErtType env ctx A
      | throwErrorAt A m!"Expected type, got {repr A}"
    return Untyped.Term.app A_term f_term a_term
  | `(ertTerm| ($t, $u)) => do
    let t_term ← elabErtTerm env ctx t
    let u_term ← elabErtTerm env ctx u
    return Untyped.Term.pair t_term u_term
  | `(ertTerm| let ($x, $y) : $A = $e in $b) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let (x_term, y_term) ←
      match A_term with
      | Untyped.Term.sigma x_term y_term => pure (x_term, y_term)
      | _ => throwErrorAt A "invalid type in let-pair"
    let e_term ← elabErtTerm env ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm env
      ((yName, Hyp.type y_term) :: (xName, Hyp.type x_term) :: ctx) b
    return Untyped.Term.let_pair .type A_term e_term b_term
  | `(ertTerm| (inl $t) : $AB:ertType) => do
    let .exprType AB_term ← elabErtType env ctx AB | throwErrorAt AB "expected type expression"
    return Untyped.Term.inj (0 : Fin 2) AB_term (← elabErtTerm env ctx t)
  | `(ertTerm| (inr $t) : $AB:ertType) => do
    let .exprType AB_term ← elabErtType env ctx AB | throwErrorAt AB "expected type expression"
    return Untyped.Term.inj (1 : Fin 2) AB_term (← elabErtTerm env ctx t)
  | `(ertTerm| cases [$x : $D ↦ $C] $d |inl ($xl : $A) ↦ $l |inr ($xr : $B) ↦ $r) => do
    let xName := x.getId
    let .exprType D_term ← elabErtType env ctx D | throwErrorAt D "expected type expression"
    let .exprType C_term ← elabErtType env ((xName, Hyp.type D_term) :: ctx) C
      | throwErrorAt C "expected type expression"
    let K_term := Untyped.Term.lam D_term C_term
    let d_term ← elabErtTerm env ctx d
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xlName := xl.getId
    let l_term ← elabErtTerm env ((xlName, Hyp.type A_term) :: ctx) l
    let xrName := xr.getId
    let .exprType B_term ← elabErtType env ctx B | throwErrorAt B "expected type expression"
    let r_term ← elabErtTerm env ((xrName, Hyp.type B_term) :: ctx) r
    return Untyped.Term.case .type K_term d_term l_term r_term
  | `(ertTerm| {$x, $p : $P} : $T) => do
    let x_term ← elabErtTerm env ctx x
    let .exprProp P_expr ← elabErtProp env ctx P | throwErrorAt P "expected prop expression"
    let p_term ← liftTermElabM $ do
      withCtxToLocalCtx env ctx [] fun fvars => do
      let expectedType := P_expr.instantiate fvars.toArray
      let proof ← Term.elabTermAndSynthesize p (some expectedType)
      return proof.abstract fvars.toArray.reverse
    let .exprType T_term ← elabErtType env ctx T | throwErrorAt T "expected expression"
    return Untyped.Term.elem x_term (Untyped.Term.proof p_term P_expr) T_term
  | `(ertTerm| let {$a, $b} : $A = $x in $e) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let (a_term, b_expr) ←
      match A_term with
      | Untyped.Term.set a_term (Untyped.Term.expr b_expr) => pure (a_term, b_expr)
      | _ => throwErrorAt A "invalid type in let-set"
    let x_term ← elabErtTerm env ctx x
    let aName := a.getId
    let bName := b.getId
    let e_term ← elabErtTerm env
      ((bName, Hyp.prop b_expr) :: (aName, Hyp.type a_term) :: ctx) e
    return Untyped.Term.let_set .type A_term x_term e_term
  | `(ertTerm| λ ‖$x : $A‖ . $t) => do
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let xName := x.getId
    let t_term ← elabErtTerm env ((xName, Hyp.type A_term) :: ctx) t
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
    let .exprType A_term ← elabErtType env ctx A | throwErrorAt A "expected type expression"
    let (x_term, y_term) ←
      match A_term with
      | Untyped.Term.union x_term y_term => pure (x_term, y_term)
      | _ => throwErrorAt A "invalid type of let-repr"
    let e_term ← elabErtTerm env ctx e
    let xName := x.getId
    let yName := y.getId
    let b_term ← elabErtTerm env
      ((yName, Hyp.type y_term) :: (xName, Hyp.type x_term) :: ctx) b
    return Untyped.Term.let_repr .type A_term e_term b_term
  | `(ertTerm| $n:num) =>
    return buildNat n.getNat
  | `(ertTerm| natrec [$x ↦ $C:ertType] $e:ertTerm | $z:ertTerm
    | ‖succ $xs:ident‖ , $xp ↦ $s) => do
    let xName := x.getId
    let .exprType K_term ← elabErtType env
        ((xName, Hyp.type Untyped.Term.nats) :: ctx) C
      | throwErrorAt C "expected type expression"
    let e_term ← elabErtTerm env ctx e
    let z_term ← elabErtTerm env ctx z
    let xsName := xs.getId
    let xpName := xp.getId
    let s_term ← elabErtTerm env
        ((xpName, Hyp.type K_term) :: (xsName, Hyp.type Untyped.Term.nats) :: ctx) s
    return Untyped.Term.natrec .type K_term e_term z_term s_term
  | `(ertTerm| ($t)) => elabErtTerm env ctx t
  | `(ertTerm| nil : $A) => do
    let .exprType A_term ← elabErtType env ctx A
      | throwErrorAt A "expected type expression"
    return Untyped.Term.em A_term
  | `(ertTerm| $x :: $xs) => do
    let x_term ← elabErtTerm env ctx x
    let xs_term ← elabErtTerm env ctx xs
    return Untyped.Term.cons x_term xs_term
  | `(ertTerm| listrec [($xs : $T) ↦ $C:ertType] $e:ertTerm | $em:ertTerm
      | $hd:ident , $tl:ident , $ih:ident ↦ $c) => do
    let xsName := xs.getId
    let hdName := hd.getId
    let tlName := tl.getId
    let ihName := ih.getId
    let .exprType T_term ← elabErtType env ctx T
      | throwErrorAt T m!"invalid type"
    -- The motive's bound variable has the user-given list type T;
    -- the element type is extracted for hd.
    let elem_term ← match T_term with
      | Untyped.Term.list e => pure e
      | _ => throwErrorAt T m!"listrec motive binder must have a list type"
    let .exprType K_term ← elabErtType env
        ((xsName, Hyp.type T_term) :: ctx) C
      | throwErrorAt C "expected type expression"
    let e_term ← elabErtTerm env ctx e
    let em_term ← elabErtTerm env ctx em
    -- cons case binders (innermost first):
    --   var 0 = ih  (type C[tl / motive_var])
    --   var 1 = tl  (type list elem)
    --   var 2 = hd  (type elem)
    -- Stored types are in just-below-binder context, matching Subst.lookupVar's
    -- automatic wk1 application as we descend.
    let c_term ← elabErtTerm env
        ((ihName, Hyp.type (K_term.lift 1 1)) ::
         (tlName, Hyp.type T_term.wk1) ::
         (hdName, Hyp.type elem_term) :: ctx) c
    return Untyped.Term.listrec .type K_term e_term em_term c_term
  | stx => throwErrorAt stx "Unsupported ERT term: {stx}"

end

def addStatementToLeanEnv (env : Env) (name : Name) (type term : Untyped.Term) :
    CommandElabM Unit := do
  let typeExpr ← liftTermElabM $ do instantiateMVars (← type.toExpr env [])
  let termExpr ← liftTermElabM $ do instantiateMVars (← term.toExpr env [])
  if typeExpr.hasMVar then
    throwError "unresolved metavariables in elaborated type: {typeExpr}"
  if termExpr.hasMVar then
    throwError "unresolved metavariables in elaborated term: {termExpr}"
  liftTermElabM $ addAndCompile <| .defnDecl {
    name        := name
    levelParams := []
    type        := typeExpr
    value       := termExpr
    hints       := .regular 0
    safety      := .safe
  }
  liftTermElabM $ enableRealizationsForConst name
  elabCommand (← `(command| attribute [grind] $(mkIdent name)))

def elabErtStatement (env : List Statement) : Syntax → CommandElabM Statement
  | `(ertStatement| def $name : $ty:ertType := $body) => do
    let annot@(.exprType type) ← elabErtType env [] ty | throwErrorAt ty "expected a type"
    let term ← elabErtTerm env [] body
    try
      liftTermElabM $ Check.check env term annot
      addStatementToLeanEnv env name.getId type term
      return .defn name.getId type term
    catch msg =>
      throwErrorAt name msg.toMessageData
  | `(ertStatement| def $name : $prop:term := $body:term) => do
    let .exprProp prop ← elabErtProp env [] prop | throwErrorAt prop "expected prop expression"
    let bodyExpr ← liftTermElabM $ Term.elabTermAndSynthesize body prop
    if ← liftTermElabM $ isDefEq prop (← liftTermElabM $ Meta.inferType bodyExpr) then
      return .thm name.getId prop bodyExpr
    else
      throwErrorAt name "invalid proof"
  | _ => throwUnsupportedSyntax

@[command_elab ert]
def ertImpl : CommandElab := fun stx => do
  let mut env : List Statement := []
  for i in stx[2].getArgs do
    env := (← elabErtStatement env i) :: env
