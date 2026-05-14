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
| thm (name : Name) (type : Expr) (proof : Expr)
deriving BEq

def Statement.name : Statement → Name
| defn name _ _ => name
| thm name _ _ => name

def Statement.type : Statement → Untyped.Term ⊕ Expr
| defn _ type _ => .inl type
| thm _ type _ => .inr type

def succAppToNat (acc : Nat): Untyped.Term → MetaM Expr
| Untyped.Term.zero => return q($acc)
| Untyped.Term.app _ (Untyped.Term.succ) r => succAppToNat (acc + 1) r
| _ => throwError "Invalid natural number"

abbrev Env := List Statement

def Untyped.Term.toExpr (env : List Statement) (ctx : List Expr) : Term → MetaM Expr
| Term.unit => return q(Unit)
| Term.nats => return q(Nat)
| Term.nil => return q(())
| Term.zero => return q(0)
| Term.succ => return q(Nat.succ)
| Term.proof e _ => return e.instantiate ctx.toArray
| Term.expr e => return e.instantiate ctx.toArray
| Term.var v =>
  match ctx[v]? with
  | some e => return e
  | none => throwError "variable index {v} out of range (context size {ctx.length})"
| Term.pi dom cod
| Term.intersect dom cod => do
  let dom_expr ← dom.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let cod_expr ← cod.toExpr env (x :: ctx)
    mkForallFVars #[x] cod_expr
| Term.assume P_expr cod => do
  let P_inst := P_expr.instantiate ctx.toArray
  withLocalDeclD (← mkFreshUserName `x) P_inst fun x => do
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
| Term.set A (Term.expr P_expr) => do
  let A_expr ← A.toExpr env ctx
  let pred_lam ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
    let body := P_expr.instantiate (x_fvar :: ctx).toArray
    mkLambdaFVars #[x_fvar] body
  mkAppM ``Subtype #[pred_lam]
| Term.set _ b =>
  throwError m!"invalid set predicate (must be Term.expr) {_root_.repr b}"
| Term.union dom cod => do
  let dom_expr ← dom.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) dom_expr fun x => do
    let cod_expr ← cod.toExpr env (x :: ctx)
    let lam ← mkLambdaFVars #[x] cod_expr
    mkAppM ``Subtype #[lam]
| Term.lam A t
| Term.lam_irrel A t => do
  let A_expr ← A.toExpr env ctx
  withLocalDeclD (← mkFreshUserName `x) A_expr fun x => do
    let t_expr ← t.toExpr env (x :: ctx)
    mkLambdaFVars #[x] t_expr
| Term.lam_pr P_expr t => do
  let P_inst := P_expr.instantiate ctx.toArray
  withLocalDeclD (← mkFreshUserName `x) P_inst fun x => do
    let t_expr ← t.toExpr env (x :: ctx)
    mkLambdaFVars #[x] t_expr
| Term.app _ (Term.succ) r => do
  match r with
  | Term.zero | Term.app _ Term.succ _ => succAppToNat 1 r
  | _ => do
    let r_expr ← r.toExpr env ctx
    let succ_expr ← Term.succ.toExpr env ctx
    return mkApp succ_expr r_expr
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
| Term.elem val p (Term.set dom (Term.expr P_expr)) => do
  let dom_expr ← dom.toExpr env ctx
  let pred_lam ← withLocalDeclD (← mkFreshUserName `x) dom_expr fun x_fvar => do
    let body := P_expr.instantiate (x_fvar :: ctx).toArray
    mkLambdaFVars #[x_fvar] body
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
| Term.natrec _ C e z s => do
  let e_expr ← e.toExpr env ctx
  let z_expr ← z.toExpr env ctx
  -- Build motive: fun (n : Nat) => C with bvar 0 := n
  let motive ← withLocalDeclD (← mkFreshUserName `n) (mkConst ``Nat) fun n_var => do
    let body ← C.toExpr env (n_var :: ctx)
    mkLambdaFVars #[n_var] body
  -- Build step: fun (n : Nat) (ih : motive n) => body
  -- var 0 = ih, var 1 = n in the step body
  let s_lam ← withLocalDeclD (← mkFreshUserName `n) (mkConst ``Nat) fun n_var => do
    let ih_ty := mkApp motive n_var
    withLocalDeclD (← mkFreshUserName `ih) ih_ty fun ih_var => do
      let body ← s.toExpr env (ih_var :: n_var :: ctx)
      mkLambdaFVars #[n_var, ih_var] body
  mkAppOptM ``Nat.rec #[some motive, some z_expr, some s_lam, some e_expr]
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
| Term.listrec _ C lst nil_case cons_case => do
  let lst_expr ← lst.toExpr env ctx
  let nil_expr ← nil_case.toExpr env ctx
  let lst_type ← inferType lst_expr
  let A_expr ← match lst_type with
    | .app (.const ``List _) A => pure A
    | _ => throwError "listrec: subject must have type List A, got {← ppExpr lst_type}"
  let listA := mkApp (mkConst ``List [Level.zero]) A_expr
  -- Build motive: fun (ys : List A) => C with bvar 0 := ys.
  let motive ← withLocalDeclD (← mkFreshUserName `ys) listA fun ys_var => do
    let body ← C.toExpr env (ys_var :: ctx)
    mkLambdaFVars #[ys_var] body
  -- Build cons function: fun (hd : A) (tl : List A) (ih : motive tl) => body
  -- var 0 = ih, var 1 = tl, var 2 = hd in the cons case body.
  let c_lam ← withLocalDeclD (← mkFreshUserName `hd) A_expr fun hd_var => do
    withLocalDeclD (← mkFreshUserName `tl) listA fun tl_var => do
      let ih_ty := mkApp motive tl_var
      withLocalDeclD (← mkFreshUserName `ih) ih_ty fun ih_var => do
        let body ← cons_case.toExpr env (ih_var :: tl_var :: hd_var :: ctx)
        mkLambdaFVars #[hd_var, tl_var, ih_var] body
  mkAppOptM ``List.rec
    #[some A_expr, some motive, some nil_expr, some c_lam, some lst_expr]
| Untyped.Term.const (Untyped.TermKind.definition defName) => do
  return mkConst defName
| a => throwError m!"unhandled proof term {_root_.repr a}"

def Untyped.Term.getMaxBVarIdx (t : Term) : Nat := go 0 t
where
  go (curr : Nat) : Term → Nat
  | var (v: Nat) => max v curr
  | proof p Ty => max curr (max (p.looseBVarRange - 1) (Ty.looseBVarRange - 1))
  | expr (e : Lean.Expr) => max curr (e.looseBVarRange - 1)
  | const (_: TermKind []) => curr
  | unary (_: TermKind [0]) (t: Term) => max curr (go curr t)
  | let_bin (_: TermKind [0, 0, 2]) (P: Term) (e: Term) (e': Term) =>
    max curr (max (go curr P) (max (go curr e) (go curr e')))
  | let_bin_beta (_: TermKind [0, 0, 0, 2]) (P: Term) l r (e': Term) =>
    max curr (max (go curr P) (max (go curr l) (max (go curr r) (go curr e'))))
  | bin (_: TermKind [0, 0]) (l: Term) (r: Term) =>
    max curr (max (go curr l) (go curr r))
  | abs (_: TermKind [0, 1]) (A: Term) (t: Term) =>
    max curr (max (go curr A) (go curr t))
  | pabs (_: TermKind [0, 1]) (A: Lean.Expr) (t: Term) =>
    max curr (max (A.looseBVarRange - 1) (go curr t))
  | tri (_: TermKind [0, 0, 0]) (A: Term) (l: Term) (r: Term) =>
    max curr (max (go curr A) (max (go curr l) (go curr r)))
  | ir (_: TermKind [0, 0, 1]) (x: Term) (y: Term) (P: Term) =>
    max curr (max (go curr x) (max (go curr y) (go curr P)))
  | cases (_: TermKind [0, 0, 1, 1]) (K: Term) (d: Term) (l: Term) (r: Term) =>
    max curr (max (go curr K) (max (go curr d) (max (go curr l) (go curr r))))
  | nr (_: TermKind [1, 0, 0, 2]) (K: Term) (e: Term) (z: Term) (s: Term) =>
    max curr (max (go curr K) (max (go curr e) (max (go curr z) (go curr s))))
  | nz (_: TermKind [1, 0, 2]) (K: Term) (z: Term) (s: Term) =>
    max curr (max (go curr K) (max (go curr z) (go curr s)))
  | lr (_ : TermKind [1, 0, 0, 3]) (K : Term) (e : Term) (emm : Term) (c : Term) =>
    max curr (max (go curr K) (max (go curr e) (max (go curr emm) (go curr c))))

/--
  Context-less conversion of `Term` to `Lean.Expr`. Unlike `toExpr`, variables
  become loose `.bvar`s and binders are constructed directly with `.lam` /
  `.forallE`, so no fresh fvars or `mkFreshUserName` are needed. Universes for
  polymorphic constants (`Sigma`, `Sum`, `Subtype`, `Sigma.mk`, …) are filled
  with fresh level mvars and resolved during elaboration of the final term.

  Used by `Term.subst` to substitute `Term`s into loose bvars inside embedded
  `.expr`/`.proof` payloads. Some elimination cases (`Sigma.casesOn`, `Sum.casesOn`,
  `Nat.rec`, `List.foldr`) are not supported here because they need types that
  aren't recoverable from the `Term` alone — they throw if encountered.
-/
partial def Untyped.Term.toExprBVars : Term → MetaM Expr
| Term.unit => return mkConst ``Unit
| Term.nats => return mkConst ``Nat
| Term.nil => return mkConst ``Unit.unit
| Term.zero => return mkNatLit 0
| Term.succ => return mkConst ``Nat.succ
| Term.proof e _ => return e
| Term.expr e => return e
| Term.var v => return .bvar v
| Term.pi dom cod
| Term.intersect dom cod => do
  return .forallE `x (← dom.toExprBVars) (← cod.toExprBVars) .default
| Term.assume P cod => do
  return .forallE `x P (← cod.toExprBVars) .default
| Term.sigma dom cod => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let d ← dom.toExprBVars
  let c ← cod.toExprBVars
  return mkApp2 (mkConst ``Sigma [u, v]) d (.lam `x d c .default)
| Term.coprod l r => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  return mkApp2 (mkConst ``Sum [u, v]) (← l.toExprBVars) (← r.toExprBVars)
| Term.set A (Term.expr P) => do
  let u ← mkFreshLevelMVar
  let d ← A.toExprBVars
  return mkApp2 (mkConst ``Subtype [u]) d (.lam `x d P .default)
| Term.set A b => do
  let u ← mkFreshLevelMVar
  let d ← A.toExprBVars
  return mkApp2 (mkConst ``Subtype [u]) d (.lam `x d (← b.toExprBVars) .default)
| Term.union dom cod => do
  let u ← mkFreshLevelMVar
  let d ← dom.toExprBVars
  return mkApp2 (mkConst ``Subtype [u]) d (.lam `x d (← cod.toExprBVars) .default)
| Term.lam A t
| Term.lam_irrel A t => do
  return .lam `x (← A.toExprBVars) (← t.toExprBVars) .default
| Term.lam_pr P t => do
  return .lam `x P (← t.toExprBVars) .default
| Term.app _ Term.succ r => do
  return mkApp (mkConst ``Nat.succ) (← r.toExprBVars)
| Term.app _ f x
| Term.app_pr _ f x
| Term.app_irrel _ f x => do
  return mkApp (← f.toExprBVars) (← x.toExprBVars)
| Term.pair l r => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  let β ← mkFreshExprMVar none
  return mkAppN (mkConst ``Sigma.mk [u, v]) #[α, β, ← l.toExprBVars, ← r.toExprBVars]
| Term.elem val p _ => do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  let pred ← mkFreshExprMVar none
  return mkAppN (mkConst ``Subtype.mk [u]) #[α, pred, ← val.toExprBVars, ← p.toExprBVars]
| Term.repr l r => do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  let pred ← mkFreshExprMVar none
  return mkAppN (mkConst ``Subtype.mk [u]) #[α, pred, ← l.toExprBVars, ← r.toExprBVars]
| Term.bin (TermKind.inj b) _ t => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  let β ← mkFreshExprMVar none
  let ctor := if b.val == 0 then ``Sum.inl else ``Sum.inr
  return mkAppN (mkConst ctor [u, v]) #[α, β, ← t.toExprBVars]
| Term.list A => do
  let u ← mkFreshLevelMVar
  return mkApp (mkConst ``List [u]) (← A.toExprBVars)
| Term.em _ => do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  return mkApp (mkConst ``List.nil [u]) α
| Term.cons x xs => do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  return mkAppN (mkConst ``List.cons [u]) #[α, ← x.toExprBVars, ← xs.toExprBVars]
| Untyped.Term.const (Untyped.TermKind.definition defName) =>
  return mkConst defName
| a => throwError m!"toExprBVars: unsupported term {_root_.repr a}"

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
      match t with
      | .prop ty =>
        withLocalDeclD name (ty.instantiate acc'.toArray) fun x =>
          k (x :: acc')
      | .gst ty
      | .type ty =>
        withLocalDeclD name (← ty.toExpr env acc') fun x =>
          k (x :: acc')

/-- Variant that does not require names to be given.  -/
def withCtxToLocalCtx' {α : Type} (env : List Statement) (ctx : Ctx) (acc : List Expr)
    (k : List Expr → TermElabM α) : TermElabM α :=
  match ctx with
  | [] => k acc
  | t :: ts =>
    withCtxToLocalCtx' env ts acc fun acc' => do
      match t with
      | .prop ty =>
        withLocalDeclD (← mkFreshUserName `x) (ty.instantiate acc'.toArray) fun x =>
          k (x :: acc')
      | .gst ty
      | .type ty =>
        withLocalDeclD (← mkFreshUserName `x) (← ty.toExpr env acc') fun x =>
          k (x :: acc')
