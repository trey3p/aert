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
deriving BEq, Repr

-- inferType mirrors HasType as a decision procedure.
-- Deviations from old-ert's HasType:
--   - abort, ir, nz: not inferrable (see bottom).

/--
inferType Γ fvars e returns the annotation for e if it can be inferred to be well-typed in Γ,
and throws an error with a message describing the failure otherwise.
Γ is a context within the aert type theory, fvars is a list of free variables corresponding to the conversion of Γ to lean.
e is a term withing the aert type theory.
Invariant:
  fvars[i] is always a valid fvar in the current MetaM local context.
  This requires the initkal fvars passed to inferType to be created by the caller's withLocalDeclD, and
  every extension to fvars in inferType to happen within a withLocalDeclD.
--/
def inferType (Γ : Ctx) (ρ : Env) (fvars : List Expr) (e : Term) : MetaM Annot :=
  match e with
  | Term.proof k p => do
    let p_expr ← p.toExpr ρ fvars
    let k_ty ← Meta.inferType (mkAppN k fvars.toArray)
    if ← isDefEq k_ty p_expr then
      return .expr .prop p
    else
      throwError m!"proof: type mismatch"
  -- Variables: ghost bindings are not directly usable as values
  | Term.var n =>
    match lookupVar Γ n with
    | some (HypKind.val s, A) => return .expr s A
    | _ => throwError m!"var: variable {n} not found or is ghost in context"

  -- ── Constants ─────────────────────────────────────────────────────────────

  | Term.const TermKind.unit  => return .sort .type
  | Term.const TermKind.nats  => return .sort .type
  | Term.const TermKind.top   => return .sort .prop
  | Term.const TermKind.bot   => return .sort .prop
  | Term.const TermKind.nil   => return .expr .type Term.unit
  | Term.const TermKind.zero  => return .expr .type Term.nats
  -- succ : nats → nats  (pi nats nats is correct since nats is closed)
  | Term.const TermKind.succ  => return .expr .type (Term.abs TermKind.pi Term.nats Term.nats)
  --| Term.const TermKind.triv  => return .expr .prop Term.top

  -- ── Type formers ──────────────────────────────────────────────────────────

  | Term.abs TermKind.pi A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"pi: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"pi: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.sigma A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"sigma: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"sigma: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.set A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .prop => return .sort .type
      | a => throwError m!"set: predicate {repr B} must be a prop, got {repr a}"
    | a => throwError m!"set: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.assume φ A => do
    match ← inferType Γ ρ fvars φ with
    | .sort .prop =>
      let φ_expr ← φ.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) ρ (x :: fvars) A
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"assume: body {repr A} must be a type, got {repr a}"
    | a => throwError m!"assume: hypothesis {repr φ} must be a prop, got {repr a}"

  | Term.abs TermKind.intersect A B => do
  match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"intersect: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"intersect: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.union A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"union: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"union: domain {repr A} must be a type, got {repr a}"

  | Term.bin TermKind.coprod A B => do
    match ← inferType Γ ρ fvars A, ← inferType Γ ρ fvars B with
    | .sort .type, .sort .type => return .sort .type
    | aA, aB => throwError m!"coprod: both sides must be types, got {repr aA} and {repr aB}"

  -- ── Proposition formers ───────────────────────────────────────────────────

  | Term.abs TermKind.dand φ ψ => do
    match ← inferType Γ ρ fvars φ with
    | .sort .prop =>
      let φ_expr ← φ.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) ρ (x :: fvars) ψ
      match res with
      | .sort .prop => return .sort .prop
      | a => throwError m!"dand: body {repr ψ} must be a prop, got {repr a}"
    | a => throwError m!"dand: left {repr φ} must be a prop, got {repr a}"

  | Term.abs TermKind.dimplies φ ψ => do
    match ← inferType Γ ρ fvars φ with
    | .sort .prop =>
      let φ_expr ← φ.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) ρ (x :: fvars) ψ
      match res with
      | .sort .prop => return .sort .prop
      | a => throwError m!"dimplies: body {repr ψ} must be a prop, got {repr a}"
    | a => throwError m!"dimplies: antecedent {repr φ} must be a prop, got {repr a}"

  | Term.abs TermKind.forall_ A φ => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) ρ (x :: fvars) φ
      match res with
      | .sort .prop => return .sort .prop
      | a => throwError m!"forall: body {repr φ} must be a prop, got {repr a}"
    | a => throwError m!"forall: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.exists_ A φ => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) ρ (x :: fvars) φ
      match res with
      | .sort .prop => return .sort .prop
      | a => throwError m!"exists: body {repr φ} must be a prop, got {repr a}"
    | a => throwError m!"exists: domain {repr A} must be a type, got {repr a}"

  | Term.bin TermKind.or φ ψ => do
    match ← inferType Γ ρ fvars φ, ← inferType Γ ρ fvars ψ with
    | .sort .prop, .sort .prop => return .sort .prop
    | aφ, aψ => throwError m!"or: both sides must be props, got {repr aφ} and {repr aψ}"

  -- ── Term introductions ────────────────────────────────────────────────────

  -- lam A s : pi A B  when s : B in (A :: Γ)
  | Term.abs TermKind.lam A s => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.val A .type :: Γ) ρ (x :: fvars) s
      match res with
      | .expr .type B => return .expr .type (Term.abs TermKind.pi A B)
      | a => throwError m!"lam: body {repr s} must have a type, got {repr a}"
    | a => throwError m!"lam: domain {repr A} must be a type, got {repr a}"

  -- lam_pr φ s : assume φ A  when s : A in (φ :: Γ)
  | Term.abs TermKind.lam_pr φ s => do
    match ← inferType Γ ρ fvars φ with
    | .sort .prop =>
      let φ_expr ← φ.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) φ_expr fun x =>
        inferType (Hyp.val φ .prop :: Γ) ρ (x :: fvars) s
      match res with
      | .expr .type A => return .expr .type (Term.abs TermKind.assume φ A)
      | a => throwError m!"lam_pr: body {repr s} must have a type, got {repr a}"
    | a => throwError m!"lam_pr: hypothesis {repr φ} must be a prop, got {repr a}"

  -- lam_irrel A s : intersect A B  when s : B in (‖A‖ :: Γ)
  | Term.abs TermKind.lam_irrel A s => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) ρ (x :: fvars) s
      match res with
      | .expr .type B => return .expr .type (Term.abs TermKind.intersect A B)
      | a => throwError m!"lam_irrel: body {repr s} must have a type, got {repr a}"
    | a => throwError m!"lam_irrel: domain {repr A} must be a type, got {repr a}"

  -- ── Function / proof eliminations ─────────────────────────────────────────

  -- app (pi A B) f x : term (B.subst0 x)
  | Term.app _ f x => do
    match ← inferType Γ ρ fvars f with
    | .expr .type (Term.abs TermKind.pi A B) =>
      match ← inferType Γ ρ fvars x with
      | .expr .type A' =>
          if A == A' then return .expr .type (B.subst0 x)
          else throwError m!"app: argument type mismatch: expected {repr A}, got {repr A'}"
      | a => throwError m!"app: argument {repr x} must have a type, got {repr a}"
    | a => throwError m!"app: function {repr f} must have a pi type, got {repr a}"

  -- app_pr (assume φ A) l r : term (A.subst0 r)
  | Term.tri TermKind.app_pr _ l r => do
    match ← inferType Γ ρ fvars l with
    | .expr .type (Term.abs TermKind.assume φ A) =>
      match ← inferType Γ ρ fvars r with
      | .expr .prop φ' =>
          if φ == φ' then return .expr .type (A.subst0 r)
          else throwError m!"app_pr: proof type mismatch: expected {repr φ}, got {repr φ'}"
      | a => throwError m!"app_pr: right argument {repr r} must be a proof, got {repr a}"
    | a => throwError m!"app_pr: left argument {repr l} must have an assume type, got {repr a}"

  -- app_irrel (intersect A B) l r : term (B.subst0 r)
  -- r is a ghost argument: checked under Γ.upgrade
  | Term.tri TermKind.app_irrel _ l r => do
    match ← inferType Γ ρ fvars l with
    | .expr .type (Term.abs TermKind.intersect A B) =>
      match ← inferType (Ctx.upgrade Γ) ρ fvars r with
      | .expr .type A' =>
          if A == A' then return .expr .type (B.subst0 r)
          else throwError m!"app_irrel: argument type mismatch: expected {repr A}, got {repr A'}"
      | a => throwError m!"app_irrel: right argument {repr r} must have a type, got {repr a}"
    | a => throwError m!"app_irrel: left argument {repr l} must have an intersect type, got {repr a}"

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
    match ← inferType Γ ρ fvars l, ← inferType Γ ρ fvars r with
    | .expr .type A, .expr .type B_r =>
        return .expr .type (Term.abs TermKind.sigma A B_r.wk1)
    | aL, aR => throwError m!"pair: both components must have types, got {repr aL} and {repr aR}"

  -- elem l r : term (set A P)
  -- When l = var k, P is obtained by abstracting var k from φ_r (so P.subst0(var k) = φ_r).
  -- Otherwise falls back to the wk1 trick: P = φ_r.wk1.
  | Term.elem l r Ty => do
    match Ty with
    | .set domTy predicate =>
      match ← inferType Γ ρ fvars l, ← inferType Γ ρ fvars r with
      | .expr .type A, .expr .prop φ_r =>
        unless domTy == A do
          throwError m!"elem: expected domain type to be {repr domTy}, got {repr A}"
        let instantiatedPredicate := predicate.subst0 l
        unless φ_r == instantiatedPredicate do
          throwError m!"elem: proof has the wrong types, expected {repr instantiatedPredicate}, got {repr φ_r}"
        return .expr .type Ty
      | aL, aR => throwError m!"elem: expected (type, prop), got {repr aL} and {repr aR}"
    | x => throwError m!"elem: expected type to be a set, got {repr x}"

  -- repr l r : term (union A (B_r.wk1))
  -- l is the ghost witness: checked under Γ.upgrade
  -- ∪ x : A, B x
  | Term.bin TermKind.repr l r => do
    match ← inferType (Ctx.upgrade Γ) ρ fvars l, ← inferType Γ ρ fvars r with
    | .expr .type A, .expr .type B_r =>
        return .expr .type (Term.abs TermKind.union A B_r.wk1)
    | aL, aR => throwError m!"repr: both components must have types, got {repr aL} and {repr aR}"

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
    let nats_expr ← Term.nats.toExpr ρ fvars
    let res_C ← withLocalDeclD (← mkFreshUserName `n) nats_expr fun n_fvar =>
      inferType (Hyp.val Term.nats :: Γ) ρ (n_fvar :: fvars) C
    match res_C with
    | .sort .type =>
      match ← inferType Γ ρ fvars e with
      | .expr .type (Term.const TermKind.nats) =>
        match ← inferType Γ ρ fvars z with
        | .expr .type z_ty =>
          if z_ty == C.subst0 Term.zero then
            let succ_app := Term.tri TermKind.app
                              (Term.abs TermKind.pi Term.nats Term.nats)
                              Term.succ (Term.var 1)
            let step_ty  := (C.lift 1 1).alpha0 succ_app
            let step_ctx := Hyp.val C .type :: Hyp.gst Term.nats :: Γ
            let res_s ← withLocalDeclD (← mkFreshUserName `n) nats_expr fun n_fvar => do
              let C_n ← C.toExpr ρ (n_fvar :: fvars)
              withLocalDeclD (← mkFreshUserName `ih) C_n fun ih_fvar =>
                inferType step_ctx ρ (ih_fvar :: n_fvar :: fvars) s
            match res_s with
            | .expr .type s_ty =>
                if s_ty == step_ty then return .expr .type (C.subst0 e)
                else throwError m!"natrec: step type mismatch: expected {repr step_ty}, got {repr s_ty}"
            | a => throwError m!"natrec: step {repr s} must have a type, got {repr a}"
          else throwError m!"natrec: base case type mismatch: expected {repr (C.subst0 Term.zero)}, got {repr z_ty}"
        | a => throwError m!"natrec: base case {repr z} must have a type, got {repr a}"
      | a => throwError m!"natrec: subject {repr e} must have type nats, got {repr a}"
    | a => throwError m!"natrec: motive {repr C} must be a type, got {repr a}"

  -- ── Coproduct introduction ────────────────────────────────────────────────

  -- inj 0 B t : coprod T B  when t : T  (inl, annotated with right type B)
  -- inj 1 A t : coprod A T  when t : T  (inr, annotated with left type A)
  | Term.bin (TermKind.inj b) annot t => do
    match annot with
    | Term.bin TermKind.coprod A B =>
      match ← inferType Γ ρ fvars annot with
      | .sort .type =>
        match ← inferType Γ ρ fvars t with
        | .expr .type T =>
          if b.val == 0 && T == A then
            return .expr .type (Term.bin TermKind.coprod A B)
          else
            return .expr .type (Term.bin TermKind.coprod A B)
        | a => throwError m!"inj: term {repr t} must have a type, got {repr a}"
      | a => throwError m!"inj: annotation {repr annot} must be a type, got {repr a}"
    | _ => throwError m!"inj: annotation must be a coprod type"

  -- ── Coproduct elimination ─────────────────────────────────────────────────

  -- case .type (lam D C) d l r : C.subst0 d
  --   d : coprod A B
  --   l in (val A .type :: Γ) : C.alpha0 (inl (var 0))   (left branch)
  --   r in (val B .type :: Γ) : C.alpha0 (inr (var 0))   (right branch)
  -- A and B come from d's inferred type; the motive body C is extracted from K.
  -- B.wk1 / A.wk1 shift the annotation into the branch context.
  | Term.cases (TermKind.case .type) K d l r => do
    match ← inferType Γ ρ fvars d with
    | .expr .type (Term.bin TermKind.coprod A B) =>
      match K with
      | Term.abs TermKind.lam _ C =>
        let A_expr ← A.toExpr ρ fvars
        let B_expr ← B.toExpr ρ fvars
        let l_ty := C.alpha0 (Term.bin (TermKind.inj (0 : Fin 2)) B.wk1 (Term.var 0))
        let r_ty := C.alpha0 (Term.bin (TermKind.inj (1 : Fin 2)) A.wk1 (Term.var 0))
        let l_result ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar =>
          inferType (Hyp.val A .type :: Γ) ρ (x_fvar :: fvars) l
        let r_result ← withLocalDeclD (← mkFreshUserName `y) B_expr fun y_fvar =>
          inferType (Hyp.val B .type :: Γ) ρ (y_fvar :: fvars) r
        match l_result, r_result with
        | .expr .type l_ty', .expr .type r_ty' =>
          if l_ty' == l_ty && r_ty' == r_ty then
            return .expr .type (C.subst0 d)
          else throwError m!"case: branch type mismatch"
        | aL, aR => throwError m!"case: branches must have types, got {repr aL} and {repr aR}"
      | _ => throwError m!"case: motive {repr K} must be a lam"
    | a => throwError m!"case: discriminant {repr d} must have coprod type, got {repr a}"

  -- ── Dependent pair / set / union eliminations ────────────────────────────
  -- P carries the type of e; the body context adds two binders (inner first):
  --   let_pair  P = sigma A B :  var 0 = y : B.wk1,  var 1 = x : A
  --   let_set   P = set A φ   :  var 0 = h : φ.wk1,  var 1 = x : A
  --   let_repr  P = union A B :  var 0 = y : B.wk1,  var 1 = x : A (ghost)


  | Term.let_bin (TermKind.let_pair .type) P e e' => do
    match P with
    | Term.abs TermKind.sigma A B =>
      match ← inferType Γ ρ fvars e with
      | .expr .type P' =>
        if P' != P then throwError m!"let_pair: scrutinee type {repr P'} does not match annotation {repr P}"
        let A_expr ← A.toExpr ρ fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let B_x ← B.toExpr ρ (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `y) B_x fun y_fvar => do
            match ← inferType (Hyp.val B.wk1 .type :: Hyp.val A .type :: Γ)
                               ρ (y_fvar :: x_fvar :: fvars) e' with
            | .expr .type T_ext => return .expr .type T_ext
            | a => throwError m!"let_pair: body {repr e'} must have a type, got {repr a}"
      | a => throwError m!"let_pair: scrutinee {repr e} must have a type, got {repr a}"
    | _ => throwError m!"let_pair: annotation must be a sigma type"

  | Term.let_bin (TermKind.let_set .type) P e e' => do
    match P with
    | Term.abs TermKind.set A φ =>
      match ← inferType Γ ρ fvars e with
      | .expr .type P' =>
        if P' != P then throwError m!"let_set: scrutinee type {repr P'} does not match annotation {repr P}"
        let A_expr ← A.toExpr ρ fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let φ_x ← φ.toExpr ρ (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `h) φ_x fun h_fvar => do
            match ← inferType (Hyp.val φ .prop :: Hyp.val A .type :: Γ)
                               ρ (h_fvar :: x_fvar :: fvars) e' with
            | .expr .type T_ext => return .expr .type T_ext
            | a => throwError m!"let_set: body {repr e'} must have a type, got {repr a}"
      | a => throwError m!"let_set: scrutinee {repr e} must have a type, got {repr a}"
    | _ => throwError m!"let_set: annotation must be a set type"

  | Term.let_bin (TermKind.let_repr .type) P e e' => do
    match P with
    | Term.abs TermKind.union A B =>
      match ← inferType Γ ρ fvars e with
      | .expr .type P' =>
        if P' != P then throwError m!"let_repr: scrutinee type {repr P'} does not match annotation {repr P}"
        let A_expr ← A.toExpr ρ fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let B_x ← B.toExpr ρ (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `y) B_x fun y_fvar => do
            match ← inferType (Hyp.val B.wk1 .type :: Hyp.gst A :: Γ)
                               ρ (y_fvar :: x_fvar :: fvars) e' with
            | .expr .type T_ext => return .expr .type T_ext
            | a => throwError m!"let_repr: body {repr e'} must have a type, got {repr a}"
      | a => throwError m!"let_repr: scrutinee {repr e} must have a type, got {repr a}"
    | _ => throwError m!"let_repr: annotation must be a union type"

  | Term.eq A l r => do
    match ← inferType Γ ρ fvars l with
    | .expr .type L =>
      if L == A then
        match ← inferType Γ ρ fvars r with
        | .expr .type R =>
            if R == A then
              return .sort .prop
            else
              throwError m!"eq: RHS {repr r} must have type {repr A}, got {repr R}"
        | a => throwError m!"eq: RHS {repr r} must have type {repr A}, got {repr a}"
      else
        throwError m!"eq: LHS {repr l} must have type {repr A}, got {repr L}"
    | a => throwError m!"eq: LHS {repr l} must have type {repr A}, got {repr a}"
  | Term.list A => do
    match ← inferType Γ ρ fvars A with
    | .expr .type _ => return .sort .type
    | a => throwError m!"list: element type {repr A} must have a type, got {repr a}"
  | Term.em A => do
    match ← inferType Γ ρ fvars A with
    | .expr .type _ => return .sort .type
    | a => throwError m!"[]: element type {repr A} must have a type, got {repr a}"
  | Term.cons A x xs => do
    match ← inferType Γ ρ fvars A with
    | .expr .type _ =>
      match ← inferType Γ ρ fvars x with
      | .expr .type x_ty =>
          if x_ty == A then
            match ← inferType Γ ρ fvars xs with
            | .expr .type xs_ty =>
                if xs_ty == Term.list A then return .expr .type (Term.list A)
                else throwError m!"cons: tail {repr xs} must have type list {repr A}, got {repr xs_ty}"
            | a => throwError m!"cons: tail {repr xs} must have type list {repr A}, got {repr a}"
          else throwError m!"cons: head {repr x} must have type {repr A}, got {repr x_ty}"
      | a => throwError m!"cons: head {repr x} must have type {repr A}, got {repr a}"
    | a => throwError m!"cons: element type {repr A} must have a type, got {repr a}"
  | Term.listrec C e nil_case cons_case => do
      match ← inferType Γ ρ fvars e with
      | .expr .type (Term.list A) =>
        let A_expr ← A.toExpr ρ fvars
        let res_C ← withLocalDeclD (← mkFreshUserName `xs) (Term.list A).toExpr ρ fvars fun xs_fvar =>
          inferType (Hyp.val (Term.list A) .type :: Γ) ρ (xs_fvar :: fvars) C
        match res_C with
        | .sort .type =>
          let nil_ty := C.subst0 Term.nil
          let cons_ty := (C.lift 1 1).alpha0 (Term.bin TermKind.cons A (Term.var 1) (Term.var 0))
          match ← inferType Γ ρ fvars nil_case with
          | .expr .type nil_case_ty =>
              if nil_case_ty == nil_ty then
                let cons_ctx := Hyp.val C .type :: Hyp.val A .type :: Hyp.val (Term.list A) .type :: Γ
                let res_cons_case ← withLocalDeclD (← mkFreshUserName `xs) (Term.list A).toExpr ρ fvars fun xs_fvar =>
                  withLocalDeclD (← mkFreshUserName `x) A.toExpr ρ fvars fun x_fvar =>
                    withLocalDeclD (← mkFreshUserName `ih) C.subst0 (Term.var 1).toExpr ρ fvars fun ih_fvar =>
                      inferType cons_ctx ρ (ih_fvar :: x_fvar :: xs_fvar :: fvars) cons_case
                match res_cons_case with
                | .expr .type cons_case_ty =>
                    if cons_case_ty == cons_ty then return .expr .type (C.subst0 e)
                    else throwError m!"listrec: cons case type mismatch: expected {repr cons_ty}, got {repr cons_case_ty}"
                | a => throwError m!"listrec: cons case {repr cons_case} must have a type, got {repr a}"
              else throwError m!"listrec: nil case type mismatch: expected {repr nil_ty}, got {repr nil_case_ty}"
  -- ── Not inferrable without annotation ────────────────────────────────────
  -- abort       : return type is arbitrary, no annotation in term
  -- ir forms    : equality proofs (trans, cong, prir, …)
  -- nz forms    : beta-reduction proofs
  -- natrec prop : requires Γ.upgrade (not implemented)
  | _ => throwError m!"inferType: unsupported or non-inferrable term {repr e}"

end Untyped
