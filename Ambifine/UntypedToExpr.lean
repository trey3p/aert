import Ambifine.Untyped
import Ambifine.Context
import Lean
import Qq

open Lean Meta Elab Term
open Qq

abbrev NamedHyp := Name × Hyp
abbrev NamedCtx := List NamedHyp

inductive Statement where
| defn (name : Name) (type : Untyped.Term) (term : Untyped.Term)
| thm (name : Name) (type : Untyped.Term) (proof : Expr)
deriving BEq

def Statement.name : Statement → Name
| defn name _ _ => name
| thm name _ _ => name

def Statement.type : Statement → Untyped.Term
| defn _ type _ => type
| thm _ type _ => type

def succAppToNat (acc : Nat): Untyped.Term → MetaM Expr
| Untyped.Term.zero => return q($acc)
| Untyped.Term.app _ (Untyped.Term.succ) r => succAppToNat (acc + 1) r
| _ => throwError "Invalid natural number"

abbrev Env := List Statement

def Untyped.Term.toExpr (env : List Statement) (ctx : List Expr) : Term → MetaM Expr
| Term.unit => return q(Unit)
| Term.nats => return q(Nat)
| Term.top => return q(True)
| Term.bot => return q(False)
| Term.nil => return q(())
| Term.zero => return q(0)
| Term.succ => return q(Nat.succ)
| Term.proof e _ => return mkAppN e ctx.toArray.reverse
| Term.var v =>
  match ctx[v]? with
  | some e => return e
  | none => throwError "variable index {v} out of range (context size {ctx.length})"
| Term.pi dom cod
| Term.assume dom cod
| Term.intersect dom cod
| Term.dimplies dom cod
| Term.forall_ dom cod => do
  let dom_expr ← dom.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let cod_expr ← cod.toExpr env (x :: ctx)
    mkForallFVars #[x] cod_expr
| Term.sigma dom cod => do
  let dom_expr ← dom.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let cod_expr ← cod.toExpr env (x :: ctx)
    let lam ← mkLambdaFVars #[x] cod_expr
    mkAppM ``Sigma #[lam]
| Term.coprod left right => do
  let left_expr ← left.toExpr env ctx
  let right_expr ← right.toExpr env ctx
  mkAppM ``Sum #[left_expr, right_expr]
| Term.set dom cod
| Term.union dom cod => do
  let dom_expr ← dom.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let cod_expr ← cod.toExpr env (x :: ctx)
    let lam ← mkLambdaFVars #[x] cod_expr
    mkAppM ``Subtype #[lam]
| Term.dand dom cod
| Term.exists_ dom cod => do
  let dom_expr ← dom.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let cod_expr ← cod.toExpr env (x :: ctx)
    let lam ← mkLambdaFVars #[x] cod_expr
    mkAppM ``Exists #[lam]
| Term.or l r => do
  let l_expr ← l.toExpr env ctx
  let r_expr ← r.toExpr env ctx
  mkAppM ``Or #[l_expr, r_expr]
| Term.eq _ x y => do
  let x_expr ← x.toExpr env ctx
  let y_expr ← y.toExpr env ctx
  mkAppM ``Eq #[x_expr, y_expr]
| Term.lam A t
| Term.lam_pr A t
| Term.lam_irrel A t => do
  let A_expr ← A.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) A_expr fun x => do
    let t_expr ← t.toExpr env (x :: ctx)
    mkLambdaFVars #[x] t_expr
| Term.app _ (Term.succ) r => succAppToNat 1 r
| Term.app _ f x
| Term.app_pr _ f x
| Term.app_irrel _ f x => do
  let f_expr ← f.toExpr env ctx
  let x_expr ← x.toExpr env ctx
  return mkApp f_expr x_expr
| Term.pair l r => do
  let l_expr ← l.toExpr env ctx
  let r_expr ← r.toExpr env ctx
  mkAppM ``Sigma.mk #[l_expr, r_expr]
| Term.elem val p (Term.set dom pred) => do
  let dom_expr ← dom.toExpr env ctx
  let pred_lam ← withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let pred_expr ← pred.toExpr env (x :: ctx)
    mkLambdaFVars #[x] pred_expr
  let val_expr ← val.toExpr env ctx
  let proof_expr ← p.toExpr env ctx
  mkAppOptM ``Subtype.mk #[some dom_expr, some pred_lam, some val_expr, some proof_expr]
| e@(Term.elem _ _ _) => do
  throwError m!"invalid type of elem {_root_.repr e}"
| Term.repr l r => do
  let l_expr ← l.toExpr env ctx
  let r_expr ← r.toExpr env ctx
  mkAppM ``Subtype.mk #[l_expr, r_expr]
| Term.bin (TermKind.inj b) _ t => do
  let t_expr ← t.toExpr env ctx
  if b.val == 0 then
    mkAppM ``Sum.inl #[t_expr]
  else
    mkAppM ``Sum.inr #[t_expr]
| Term.let_pair _ _ e e' => do
  let e_expr ← e.toExpr env ctx
  let e'_expr ← e'.toExpr env ctx
  mkAppM ``Sigma.casesOn #[e_expr, e'_expr]
| Term.let_set _ _ e e'
| Term.let_repr _ _ e e' => do
  let e_expr ← e.toExpr env ctx
  let val_proj  := mkProj ``Subtype 0 e_expr
  let prop_proj := mkProj ``Subtype 1 e_expr
  e'.toExpr env (prop_proj :: val_proj :: ctx)
| Term.case _ _ d l r => do
  let d_expr ← d.toExpr env ctx
  let l_expr ← l.toExpr env ctx
  let r_expr ← r.toExpr env ctx
  mkAppM ``Sum.casesOn #[d_expr, l_expr, r_expr]
| Term.natrec _ _ e z s => do
  let e_expr ← e.toExpr env ctx
  let z_expr ← z.toExpr env ctx
  let s_expr ← s.toExpr env ctx
  mkAppM ``Nat.rec #[z_expr, s_expr, e_expr]
| Term.list A => do
  let A_expr ← A.toExpr env ctx
  mkAppM ``List #[A_expr]
| Term.em LA => do
  let LA_expr : Q(Type) ←  LA.toExpr env ctx
  match LA_expr with
  | ~q(List $A) => do
    mkAppOptM ``List.nil #[A]
  | _ => throwError "invalid type of list"
| Term.cons x xs => do
  let x_expr ← x.toExpr env ctx
  let xs_expr ← xs.toExpr env ctx
  mkAppM ``List.cons #[x_expr, xs_expr]
| Untyped.Term.const (Untyped.TermKind.definition defName) => do
  return mkConst defName
| a => throwError m!"unhandled proof term {_root_.repr a}"

/--
  Given a list of `Term` representing a context,
  convert each of those into an `Expr` and then add them to the
  `LocalContext`.
-/
def withCtxToLocalCtx {α : Type} (env : List Statement) (ctx : NamedCtx) (acc : List Expr)
    (k : List Expr → TermElabM α) : TermElabM α :=
  match ctx with
  | [] => k acc
  | (name, t) :: ts =>
    withCtxToLocalCtx env ts acc fun acc' => do
      withLocalDeclD name (← t.ty.toExpr env acc') fun x =>
        k (x :: acc')

/-- Variant that does not require names to be given.  -/
def withCtxToLocalCtx' {α : Type} (env : List Statement) (ctx : Ctx) (acc : List Expr)
    (k : List Expr → TermElabM α) : TermElabM α :=
  match ctx with
  | [] => k acc
  | t :: ts =>
    withCtxToLocalCtx' env ts acc fun acc' => do
      withLocalDeclD (← mkFreshUserName `x) (← t.ty.toExpr env acc') fun x =>
        k (x :: acc')
