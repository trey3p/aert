import Ambifine.Untyped
import Ambifine.Context
import Ambifine.Subst
import Ambifine.UntypedToExpr
import Lean

open Lean Meta

namespace Untyped

-- Mirrors old-ert's Annot: distinguishes "e is a type/prop" from "e has type A"
inductive Annot where
  | sort : AnnotSort → Annot
  | expr : AnnotSort → Term → Annot

-- inferType mirrors HasType as a decision procedure.
-- Deviations from old-ert's HasType:
--   - abort, ir, nz: not inferrable (see bottom).

-- Remove the outermost `n` binders from a type that lives in an n-deeper context.
-- Returns none if the term references any of the n dropped variables (i.e. the
-- elimination is dependent and we cannot compute the result type without a motive).
private def dropBinders : (depth n : Nat) → Term → Option Term
  | d, n, .proof e ty => (.proof e) <$> dropBinders d n ty
  | d, n, .var v =>
      if v < d then some (.var v)
      else if v < d + n then none
      else some (.var (v - n))
  | _, _, .const c => some (.const c)
  | d, n, .unary k t => .unary k <$> dropBinders d n t
  | d, n, .bin k l r => return .bin k (← dropBinders d n l) (← dropBinders d n r)
  | d, n, .abs k A body =>
      return .abs k (← dropBinders d n A) (← dropBinders (d + 1) n body)
  | d, n, .tri k A l r =>
      return .tri k (← dropBinders d n A) (← dropBinders d n l) (← dropBinders d n r)
  | d, n, .ir k x y P =>
      return .ir k (← dropBinders d n x) (← dropBinders d n y) (← dropBinders (d + 1) n P)
  | d, n, .cases k K disc l r =>
      return .cases k (← dropBinders d n K) (← dropBinders d n disc)
                      (← dropBinders (d + 1) n l) (← dropBinders (d + 1) n r)
  | d, n, .let_bin k P e e' =>
      return .let_bin k (← dropBinders d n P) (← dropBinders d n e) (← dropBinders (d + 2) n e')
  | d, n, .let_bin_beta k P l r e' =>
      return .let_bin_beta k (← dropBinders d n P) (← dropBinders d n l)
                             (← dropBinders d n r) (← dropBinders (d + 2) n e')
  | d, n, .nr k K e z s =>
      return .nr k (← dropBinders (d + 1) n K) (← dropBinders d n e)
                   (← dropBinders d n z) (← dropBinders (d + 2) n s)
  | d, n, .nz k K z s =>
      return .nz k (← dropBinders (d + 1) n K) (← dropBinders d n z) (← dropBinders (d + 2) n s)

/--
inferType Γ fvars e returns some annotation for e if it can be inferred to be well-typed in Γ, and none otherwise.
Γ is a context within the aert type theory, fvars is a list of free variables corresponding to the conversion of Γ to lean.
e is a term withing the aert type theory.
Invariant:
  fvars[i] is always a valid fvar in the current MetaM local context.
  This requires the initkal fvars passed to inferType to be created by the caller's withLocalDeclD, and
  every extension to fvars in inferType to happen within a withLocalDeclD.
--/
def inferType (Γ : Ctx) (fvars : List Expr) (e : Term) : MetaM (Option Annot) :=
  match e with
  | Term.proof k p => do
    let p_expr ← p.toExpr fvars
    let k_ty ← Meta.inferType k
    if ← isDefEq k_ty p_expr then
      return some (.expr .prop p)
    else
      return none
  -- Variables: ghost bindings are not directly usable as values
  | Term.var n =>
    match lookupVar Γ n with
    | some (HypKind.val s, A) => return some (.expr s A)
    | _ => return none

  -- ── Constants ─────────────────────────────────────────────────────────────

  | Term.const TermKind.unit  => return some (.sort .type)
  | Term.const TermKind.nats  => return some (.sort .type)
  | Term.const TermKind.top   => return some (.sort .prop)
  | Term.const TermKind.bot   => return some (.sort .prop)
  | Term.const TermKind.nil   => return some (.expr .type Term.unit)
  | Term.const TermKind.zero  => return some (.expr .type Term.nats)
  -- succ : nats → nats  (pi nats nats is correct since nats is closed)
  | Term.const TermKind.succ  => return some (.expr .type (Term.abs TermKind.pi Term.nats Term.nats))
  --| Term.const TermKind.triv  => return some (.expr .prop Term.top)

  -- ── Type formers ──────────────────────────────────────────────────────────

  | Term.abs TermKind.pi A B => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) (x :: fvars) B
      match res with
      | some (.sort .type) => return some (.sort .type)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.sigma A B => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) (x :: fvars) B
      match res with
      | some (.sort .type) => return some (.sort .type)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.set A B => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) (x :: fvars) B
      match res with
      | some (.sort .prop) => return some (.sort .type)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.assume φ A => do
    match ← inferType Γ fvars φ with
    | some (.sort .prop) =>
      let φ_expr ← φ.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) (x :: fvars) A
      match res with
      | some (.sort .type) => return some (.sort .type)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.intersect A B => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) (x :: fvars) B
      match res with
      | some (.sort .type) => return some (.sort .type)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.union A B => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) (x :: fvars) B
      match res with
      | some (.sort .type) => return some (.sort .type)
      | _ => return none
    | _ => return none

  | Term.bin TermKind.coprod A B => do
    match ← inferType Γ fvars A, ← inferType Γ fvars B with
    | some (.sort .type), some (.sort .type) => return some (.sort .type)
    | _, _ => return none

  -- ── Proposition formers ───────────────────────────────────────────────────

  | Term.abs TermKind.dand φ ψ => do
    match ← inferType Γ fvars φ with
    | some (.sort .prop) =>
      let φ_expr ← φ.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) (x :: fvars) ψ
      match res with
      | some (.sort .prop) => return some (.sort .prop)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.dimplies φ ψ => do
    match ← inferType Γ fvars φ with
    | some (.sort .prop) =>
      let φ_expr ← φ.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) (x :: fvars) ψ
      match res with
      | some (.sort .prop) => return some (.sort .prop)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.forall_ A φ => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) (x :: fvars) φ
      match res with
      | some (.sort .prop) => return some (.sort .prop)
      | _ => return none
    | _ => return none

  | Term.abs TermKind.exists_ A φ => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) (x :: fvars) φ
      match res with
      | some (.sort .prop) => return some (.sort .prop)
      | _ => return none
    | _ => return none

  | Term.bin TermKind.or φ ψ => do
    match ← inferType Γ fvars φ, ← inferType Γ fvars ψ with
    | some (.sort .prop), some (.sort .prop) => return some (.sort .prop)
    | _, _ => return none

  -- ── Term introductions ────────────────────────────────────────────────────

  -- lam A s : pi A B  when s : B in (A :: Γ)
  | Term.abs TermKind.lam A s => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) (x :: fvars) s
      match res with
      | some (.expr .type B) => return some (.expr .type (Term.abs TermKind.pi A B))
      | _ => return none
    | _ => return none

  -- lam_pr φ s : assume φ A  when s : A in (φ :: Γ)
  | Term.abs TermKind.lam_pr φ s => do
    match ← inferType Γ fvars φ with
    | some (.sort .prop) =>
      let φ_expr ← φ.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) (x :: fvars) s
      match res with
      | some (.expr .type A) => return some (.expr .type (Term.abs TermKind.assume φ A))
      | _ => return none
    | _ => return none

  -- lam_irrel A s : intersect A B  when s : B in (‖A‖ :: Γ)
  | Term.abs TermKind.lam_irrel A s => do
    match ← inferType Γ fvars A with
    | some (.sort .type) =>
      let A_expr ← A.toExpr fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) (x :: fvars) s
      match res with
      | some (.expr .type B) => return some (.expr .type (Term.abs TermKind.intersect A B))
      | _ => return none
    | _ => return none

  -- ── Function / proof eliminations ─────────────────────────────────────────

  -- app (pi A B) f x : term (B.subst0 x)
  | Term.app _ f x => do
    match ← inferType Γ fvars f with
    | some (.expr .type (Term.abs TermKind.pi A B)) =>
      match ← inferType Γ fvars x with
      | some (.expr .type A') =>
          if A == A' then return some (.expr .type (B.subst0 x)) else return none
      | _ => return none
    | _ => return none

  -- app_pr (assume φ A) l r : term (A.subst0 r)
  | Term.tri TermKind.app_pr _ l r => do
    match ← inferType Γ fvars l with
    | some (.expr .type (Term.abs TermKind.assume φ A)) =>
      match ← inferType Γ fvars r with
      | some (.expr .prop φ') =>
          if φ == φ' then return some (.expr .type (A.subst0 r)) else return none
      | _ => return none
    | _ => return none

  -- app_irrel (intersect A B) l r : term (B.subst0 r)
  -- r is a ghost argument: checked under Γ.upgrade
  | Term.tri TermKind.app_irrel _ l r => do
    match ← inferType Γ fvars l with
    | some (.expr .type (Term.abs TermKind.intersect A B)) =>
      match ← inferType (Ctx.upgrade Γ) fvars r with
      | some (.expr .type A') =>
          if A == A' then return some (.expr .type (B.subst0 r)) else return none
      | _ => return none
    | _ => return none

  -- ── Proof introductions ───────────────────────────────────────────────────

  -- imp φ s : dimplies φ ψ  when s : proof ψ in (φ :: Γ)
  /-| Term.abs TermKind.imp φ s =>
    match inferType Γ φ, inferType (Hyp.val φ .prop :: Γ) s with
    | some (.sort .prop), some (.expr .prop ψ) =>
        some (.expr .prop (Term.abs TermKind.dimplies φ ψ))
    | _, _ => none-/

  -- general A s : forall_ A φ  when s : proof φ in (A :: Γ)
  /-| Term.abs TermKind.general A s =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) s with
    | some (.sort .type), some (.expr .prop φ) =>
        some (.expr .prop (Term.abs TermKind.forall_ A φ))
    | _, _ => none-/

  -- ── Dependent pair / set / union introductions ─────────────────────────────
  -- We use the wk1 trick: given l : A and r : B_r, the weakest valid type is
  -- sigma A (B_r.wk1), since (B_r.wk1).subst0 l = B_r holds definitionally.

  -- pair l r : term (sigma A (B_r.wk1))
  | Term.bin TermKind.pair l r => do
    match ← inferType Γ fvars l, ← inferType Γ fvars r with
    | some (.expr .type A), some (.expr .type B_r) =>
        return some (.expr .type (Term.abs TermKind.sigma A B_r.wk1))
    | _, _ => return none

  -- elem l r : term (set A (φ_r.wk1))
  -- {x : A | φ}
  | Term.bin TermKind.elem l r => do
    match ← inferType Γ fvars l, ← inferType Γ fvars r with
    | some (.expr .type A), some (.expr .prop φ_r) =>
        return some (.expr .type (Term.abs TermKind.set A φ_r.wk1))
    | _, _ => return none

  -- repr l r : term (union A (B_r.wk1))
  -- l is the ghost witness: checked under Γ.upgrade
  -- ∪ x : A, B x
  | Term.bin TermKind.repr l r => do
    match ← inferType (Ctx.upgrade Γ) fvars l, ← inferType Γ fvars r with
    | some (.expr .type A), some (.expr .type B_r) =>
        return some (.expr .type (Term.abs TermKind.union A B_r.wk1))
    | _, _ => return none

  -- ── Equality introductions ────────────────────────────────────────────────

  -- refl a : proof (eq A a a)
  -- Note: old-ert checks a in Γ.upgrade; we check a in Γ (sound over-approx).
  /-| Term.unary TermKind.refl a =>
    match inferType Γ a with
    | some (.expr .type A) => some (.expr .prop (Term.tri TermKind.eq A a a))
    | _ => none-/

  -- unit_unique a : proof (eq unit a nil)
  /-| Term.unary TermKind.unit_unique a =>
    match inferType Γ a with
    | some (.expr .type (Term.const TermKind.unit)) =>
        some (.expr .prop (Term.tri TermKind.eq Term.unit a Term.nil))
    | _ => none-/

  -- ── Natural number recursion ──────────────────────────────────────────────

  -- natrec type C e z s : expr type (C.subst0 e)
  --   C : type under ghost(nats)::Γ   (motive, var 0 = n)
  --   e : nats                         (subject)
  --   z : term (C.subst0 zero)         (base case)
  --   s : term ((C.lift 1 1).alpha0 (app (pi nats nats) succ (var 1)))
  --       in  (val C type) :: (val nats type) :: Γ   (step; old-ert uses gst for nats)
  | Term.nr (TermKind.natrec .type) C e z s => do
    let nats_expr ← Term.nats.toExpr fvars
    let res_C ← withLocalDeclD (← mkFreshUserName `n) nats_expr fun n_fvar =>
      inferType (Hyp.gst Term.nats :: Γ) (n_fvar :: fvars) C
    match res_C with
    | some (.sort .type) =>
      match ← inferType Γ fvars e with
      | some (.expr .type (Term.const TermKind.nats)) =>
        match ← inferType Γ fvars z with
        | some (.expr .type z_ty) =>
          if z_ty == C.subst0 Term.zero then
            let succ_app := Term.tri TermKind.app
                              (Term.abs TermKind.pi Term.nats Term.nats)
                              Term.succ (Term.var 1)
            let step_ty  := (C.lift 1 1).alpha0 succ_app
            let step_ctx := Hyp.val C .type :: Hyp.gst Term.nats :: Γ
            let res_s ← withLocalDeclD (← mkFreshUserName `n) nats_expr fun n_fvar => do
              let C_n ← C.toExpr (n_fvar :: fvars)
              withLocalDeclD (← mkFreshUserName `ih) C_n fun ih_fvar =>
                inferType step_ctx (ih_fvar :: n_fvar :: fvars) s
            match res_s with
            | some (.expr .type s_ty) =>
                if s_ty == step_ty then return some (.expr .type (C.subst0 e)) else return none
            | _ => return none
          else return none
        | _ => return none
      | _ => return none
    | _ => return none

  -- ── Coproduct introduction ────────────────────────────────────────────────

  -- inj 0 B t : coprod T B  when t : T  (inl, annotated with right type B)
  -- inj 1 A t : coprod A T  when t : T  (inr, annotated with left type A)
  | Term.bin (TermKind.inj b) annot t => do
    match annot with
    | Term.bin TermKind.coprod A B =>
      match ← inferType Γ fvars annot with
      | some (.sort .type) =>
        match ← inferType Γ fvars t with
        | some (.expr .type T) =>
          if b.val == 0 && T == A then
            return some (.expr .type (Term.bin TermKind.coprod A B))
          else
            return some (.expr .type (Term.bin TermKind.coprod A B))
        | _ => return none
      | _ => return none
    | _ => return none

  -- ── Coproduct elimination ─────────────────────────────────────────────────

  -- case .type (lam D C) d l r : C.subst0 d
  --   d : coprod A B
  --   l in (val A .type :: Γ) : C.alpha0 (inl (var 0))   (left branch)
  --   r in (val B .type :: Γ) : C.alpha0 (inr (var 0))   (right branch)
  -- A and B come from d's inferred type; the motive body C is extracted from K.
  -- B.wk1 / A.wk1 shift the annotation into the branch context.
  | Term.cases (TermKind.case .type) K d l r => do
    match ← inferType Γ fvars d with
    | some (.expr .type (Term.bin TermKind.coprod A B)) =>
      match K with
      | Term.abs TermKind.lam _ C =>
        let A_expr ← A.toExpr fvars
        let B_expr ← B.toExpr fvars
        let l_ty := C.alpha0 (Term.bin (TermKind.inj (0 : Fin 2)) B.wk1 (Term.var 0))
        let r_ty := C.alpha0 (Term.bin (TermKind.inj (1 : Fin 2)) A.wk1 (Term.var 0))
        let l_result ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar =>
          inferType (Hyp.val A .type :: Γ) (x_fvar :: fvars) l
        let r_result ← withLocalDeclD (← mkFreshUserName `y) B_expr fun y_fvar =>
          inferType (Hyp.val B .type :: Γ) (y_fvar :: fvars) r
        match l_result, r_result with
        | some (.expr .type l_ty'), some (.expr .type r_ty') =>
          if l_ty' == l_ty && r_ty' == r_ty then
            return some (.expr .type (C.subst0 d))
          else return none
        | _, _ => return none
      | _ => return none
    | _ => return none

  -- ── Dependent pair / set / union eliminations ────────────────────────────
  -- P carries the type of e; the body context adds two binders (inner first):
  --   let_pair  P = sigma A B :  var 0 = y : B.wk1,  var 1 = x : A
  --   let_set   P = set A φ   :  var 0 = h : φ.wk1,  var 1 = x : A
  --   let_repr  P = union A B :  var 0 = y : B.wk1,  var 1 = x : A (ghost)
  -- The return type is inferred from e' and `dropBinders 0 2` removes the two
  -- extra binders.  Returns none if e' has a dependent return type (uses var 0/1).

  | Term.let_bin (TermKind.let_pair .type) P e e' => do
    match P with
    | Term.abs TermKind.sigma A B =>
      match ← inferType Γ fvars e with
      | some (.expr .type P') =>
        if P' != P then return none
        let A_expr ← A.toExpr fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let B_x ← B.toExpr (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `y) B_x fun y_fvar => do
            match ← inferType (Hyp.val B.wk1 .type :: Hyp.val A .type :: Γ)
                               (y_fvar :: x_fvar :: fvars) e' with
            | some (.expr .type T_ext) =>
              return (dropBinders 0 2 T_ext).map (.expr .type)
            | _ => return none
      | _ => return none
    | _ => return none

  | Term.let_bin (TermKind.let_set .type) P e e' => do
    match P with
    | Term.abs TermKind.set A φ =>
      match ← inferType Γ fvars e with
      | some (.expr .type P') =>
        if P' != P then return none
        let A_expr ← A.toExpr fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let φ_x ← φ.toExpr (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `h) φ_x fun h_fvar => do
            match ← inferType (Hyp.val φ.wk1 .prop :: Hyp.val A .type :: Γ)
                               (h_fvar :: x_fvar :: fvars) e' with
            | some (.expr .type T_ext) =>
              return (dropBinders 0 2 T_ext).map (.expr .type)
            | _ => return none
      | _ => return none
    | _ => return none

  | Term.let_bin (TermKind.let_repr .type) P e e' => do
    match P with
    | Term.abs TermKind.union A B =>
      match ← inferType Γ fvars e with
      | some (.expr .type P') =>
        if P' != P then return none
        let A_expr ← A.toExpr fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let B_x ← B.toExpr (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `y) B_x fun y_fvar => do
            match ← inferType (Hyp.val B.wk1 .type :: Hyp.gst A :: Γ)
                               (y_fvar :: x_fvar :: fvars) e' with
            | some (.expr .type T_ext) =>
              return (dropBinders 0 2 T_ext).map (.expr .type)
            | _ => return none
      | _ => return none
    | _ => return none

  -- ── Not inferrable without annotation ────────────────────────────────────
  -- abort       : return type is arbitrary, no annotation in term
  -- ir forms    : equality proofs (trans, cong, prir, …)
  -- nz forms    : beta-reduction proofs
  -- natrec prop : requires Γ.upgrade (not implemented)
  | _ => return none

end Untyped
