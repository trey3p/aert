import Ambifine.Untyped
import Ambifine.Context
import Ambifine.Subst

namespace Untyped

-- Mirrors old-ert's Annot: distinguishes "e is a type/prop" from "e has type A"
inductive Annot where
  | sort : AnnotSort → Annot
  | expr : AnnotSort → Term → Annot

-- inferType mirrors HasType as a decision procedure.
-- Deviations from old-ert's HasType:
--   - Context upgrade (Γ.upgrade) is not applied; ghost-context checks use Γ.
--   - inj, disj, abort, case, let_bin, ir, nz: not inferrable (see bottom).
def inferType (Γ : Context) (e : Term) : Option Annot :=
  match e with

  -- Variables: ghost bindings are not directly usable as values
  | Term.var n =>
    match lookupVar Γ n with
    | some (HypKind.val s, A) => some (.expr s A)
    | _ => none

  -- ── Constants ─────────────────────────────────────────────────────────────

  | Term.const TermKind.unit  => some (.sort .type)
  | Term.const TermKind.nats  => some (.sort .type)
  | Term.const TermKind.top   => some (.sort .prop)
  | Term.const TermKind.bot   => some (.sort .prop)
  | Term.const TermKind.nil   => some (.expr .type Term.unit)
  | Term.const TermKind.zero  => some (.expr .type Term.nats)
  -- succ : nats → nats  (pi nats nats is correct since nats is closed)
  | Term.const TermKind.succ  => some (.expr .type (Term.abs TermKind.pi Term.nats Term.nats))
  | Term.const TermKind.triv  => some (.expr .prop Term.top)

  -- ── Type formers ──────────────────────────────────────────────────────────

  | Term.abs TermKind.pi A B =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) B with
    | some (.sort .type), some (.sort .type) => some (.sort .type)
    | _, _ => none

  | Term.abs TermKind.sigma A B =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) B with
    | some (.sort .type), some (.sort .type) => some (.sort .type)
    | _, _ => none

  | Term.abs TermKind.set A B =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) B with
    | some (.sort .type), some (.sort .prop) => some (.sort .type)
    | _, _ => none

  | Term.abs TermKind.assume φ A =>
    match inferType Γ φ, inferType (Hyp.val φ .prop :: Γ) A with
    | some (.sort .prop), some (.sort .type) => some (.sort .type)
    | _, _ => none

  | Term.abs TermKind.intersect A B =>
    match inferType Γ A, inferType (Hyp.gst A :: Γ) B with
    | some (.sort .type), some (.sort .type) => some (.sort .type)
    | _, _ => none

  | Term.abs TermKind.union A B =>
    match inferType Γ A, inferType (Hyp.gst A :: Γ) B with
    | some (.sort .type), some (.sort .type) => some (.sort .type)
    | _, _ => none

  | Term.bin TermKind.coprod A B =>
    match inferType Γ A, inferType Γ B with
    | some (.sort .type), some (.sort .type) => some (.sort .type)
    | _, _ => none

  -- ── Proposition formers ───────────────────────────────────────────────────

  | Term.abs TermKind.dand φ ψ =>
    match inferType Γ φ, inferType (Hyp.val φ .prop :: Γ) ψ with
    | some (.sort .prop), some (.sort .prop) => some (.sort .prop)
    | _, _ => none

  | Term.abs TermKind.dimplies φ ψ =>
    match inferType Γ φ, inferType (Hyp.val φ .prop :: Γ) ψ with
    | some (.sort .prop), some (.sort .prop) => some (.sort .prop)
    | _, _ => none

  | Term.abs TermKind.forall_ A φ =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) φ with
    | some (.sort .type), some (.sort .prop) => some (.sort .prop)
    | _, _ => none

  | Term.abs TermKind.exists_ A φ =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) φ with
    | some (.sort .type), some (.sort .prop) => some (.sort .prop)
    | _, _ => none

  | Term.bin TermKind.or φ ψ =>
    match inferType Γ φ, inferType Γ ψ with
    | some (.sort .prop), some (.sort .prop) => some (.sort .prop)
    | _, _ => none

  -- ── Term introductions ────────────────────────────────────────────────────

  -- lam A s : pi A B  when s : B in (A :: Γ)
  | Term.abs TermKind.lam A s =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) s with
    | some (.sort .type), some (.expr .type B) =>
        some (.expr .type (Term.abs TermKind.pi A B))
    | _, _ => none

  -- lam_pr φ s : assume φ A  when s : A in (φ :: Γ)
  | Term.abs TermKind.lam_pr φ s =>
    match inferType Γ φ, inferType (Hyp.val φ .prop :: Γ) s with
    | some (.sort .prop), some (.expr .type A) =>
        some (.expr .type (Term.abs TermKind.assume φ A))
    | _, _ => none

  -- lam_irrel A s : intersect A B  when s : B in (‖A‖ :: Γ)
  | Term.abs TermKind.lam_irrel A s =>
    match inferType Γ A, inferType (Hyp.gst A :: Γ) s with
    | some (.sort .type), some (.expr .type B) =>
        some (.expr .type (Term.abs TermKind.intersect A B))
    | _, _ => none

  -- ── Function / proof eliminations ─────────────────────────────────────────

  -- app (pi A B) f x : term (B.subst0 x)
  | Term.app _ f x =>
    match inferType Γ f with
    | some (.expr .type (Term.abs TermKind.pi A B)) =>
        match inferType Γ x with
        | some (.expr .type A') =>
            if A == A' then some (.expr .type (B.subst0 x)) else none
        | _ => none
    | _ => none

  -- app_pr (assume φ A) l r : term (A.subst0 r)
  | Term.tri TermKind.app_pr _ l r =>
    match inferType Γ l with
    | some (.expr .type (Term.abs TermKind.assume φ A)) =>
        match inferType Γ r with
        | some (.expr .prop φ') =>
            if φ == φ' then some (.expr .type (A.subst0 r)) else none
        | _ => none
    | _ => none

  -- app_irrel (intersect A B) l r : term (B.subst0 r)
  | Term.tri TermKind.app_irrel _ l r =>
    match inferType Γ l with
    | some (.expr .type (Term.abs TermKind.intersect A B)) =>
        match inferType Γ r with
        | some (.expr .type A') =>
            if A == A' then some (.expr .type (B.subst0 r)) else none
        | _ => none
    | _ => none

  -- mp (dimplies φ ψ) l r : proof (ψ.subst0 r)
  | Term.tri TermKind.mp _ l r =>
    match inferType Γ l with
    | some (.expr .prop (Term.abs TermKind.dimplies φ ψ)) =>
        match inferType Γ r with
        | some (.expr .prop φ') =>
            if φ == φ' then some (.expr .prop (ψ.subst0 r)) else none
        | _ => none
    | _ => none

  -- inst (forall_ A φ) l r : proof (φ.subst0 r)
  -- Note: old-ert checks r in Γ.upgrade; we check r in Γ (sound over-approx).
  | Term.tri TermKind.inst _ l r =>
    match inferType Γ l with
    | some (.expr .prop (Term.abs TermKind.forall_ A φ)) =>
        match inferType Γ r with
        | some (.expr .type A') =>
            if A == A' then some (.expr .prop (φ.subst0 r)) else none
        | _ => none
    | _ => none

  -- ── Proof introductions ───────────────────────────────────────────────────

  -- imp φ s : dimplies φ ψ  when s : proof ψ in (φ :: Γ)
  | Term.abs TermKind.imp φ s =>
    match inferType Γ φ, inferType (Hyp.val φ .prop :: Γ) s with
    | some (.sort .prop), some (.expr .prop ψ) =>
        some (.expr .prop (Term.abs TermKind.dimplies φ ψ))
    | _, _ => none

  -- general A s : forall_ A φ  when s : proof φ in (A :: Γ)
  | Term.abs TermKind.general A s =>
    match inferType Γ A, inferType (Hyp.val A .type :: Γ) s with
    | some (.sort .type), some (.expr .prop φ) =>
        some (.expr .prop (Term.abs TermKind.forall_ A φ))
    | _, _ => none

  -- ── Dependent pair / set / union introductions ─────────────────────────────
  -- We use the wk1 trick: given l : A and r : B_r, the weakest valid type is
  -- sigma A (B_r.wk1), since (B_r.wk1).subst0 l = B_r holds definitionally.

  -- pair l r : term (sigma A (B_r.wk1))
  | Term.bin TermKind.pair l r =>
    match inferType Γ l, inferType Γ r with
    | some (.expr .type A), some (.expr .type B_r) =>
        some (.expr .type (Term.abs TermKind.sigma A B_r.wk1))
    | _, _ => none

  -- elem l r : term (set A (φ_r.wk1))
  | Term.bin TermKind.elem l r =>
    match inferType Γ l, inferType Γ r with
    | some (.expr .type A), some (.expr .prop φ_r) =>
        some (.expr .type (Term.abs TermKind.set A φ_r.wk1))
    | _, _ => none

  -- repr l r : term (union A (B_r.wk1))
  -- Note: old-ert checks l in Γ.upgrade; we check l in Γ (sound over-approx).
  | Term.bin TermKind.repr l r =>
    match inferType Γ l, inferType Γ r with
    | some (.expr .type A), some (.expr .type B_r) =>
        some (.expr .type (Term.abs TermKind.union A B_r.wk1))
    | _, _ => none

  -- dconj l r : proof (dand A (B_r.wk1))
  | Term.bin TermKind.dconj l r =>
    match inferType Γ l, inferType Γ r with
    | some (.expr .prop A), some (.expr .prop B_r) =>
        some (.expr .prop (Term.abs TermKind.dand A B_r.wk1))
    | _, _ => none

  -- wit l r : proof (exists_ A (φ_r.wk1))
  -- Note: old-ert checks l in Γ.upgrade; we check l in Γ (sound over-approx).
  | Term.bin TermKind.wit l r =>
    match inferType Γ l, inferType Γ r with
    | some (.expr .type A), some (.expr .prop φ_r) =>
        some (.expr .prop (Term.abs TermKind.exists_ A φ_r.wk1))
    | _, _ => none

  -- ── Equality introductions ────────────────────────────────────────────────

  -- refl a : proof (eq A a a)
  -- Note: old-ert checks a in Γ.upgrade; we check a in Γ (sound over-approx).
  | Term.unary TermKind.refl a =>
    match inferType Γ a with
    | some (.expr .type A) => some (.expr .prop (Term.tri TermKind.eq A a a))
    | _ => none

  -- unit_unique a : proof (eq unit a nil)
  | Term.unary TermKind.unit_unique a =>
    match inferType Γ a with
    | some (.expr .type (Term.const TermKind.unit)) =>
        some (.expr .prop (Term.tri TermKind.eq Term.unit a Term.nil))
    | _ => none

  -- ── Natural number recursion ──────────────────────────────────────────────

  -- natrec type C e z s : expr type (C.subst0 e)
  --   C : type under ghost(nats)::Γ   (motive, var 0 = n)
  --   e : nats                         (subject)
  --   z : term (C.subst0 zero)         (base case)
  --   s : term ((C.lift 1 1).alpha0 (app (pi nats nats) succ (var 1)))
  --       in  (val C type) :: (val nats type) :: Γ   (step; old-ert uses gst for nats)
  | Term.nr (TermKind.natrec .type) C e z s =>
    match inferType (Hyp.gst Term.nats :: Γ) C with
    | some (.sort .type) =>
      match inferType Γ e with
      | some (.expr .type (Term.const TermKind.nats)) =>
        match inferType Γ z with
        | some (.expr .type z_ty) =>
          if z_ty == C.subst0 Term.zero then
            let succ_app := Term.tri TermKind.app
                              (Term.abs TermKind.pi Term.nats Term.nats)
                              Term.succ (Term.var 1)
            let step_ty  := (C.lift 1 1).alpha0 succ_app
            let step_ctx := Hyp.val C .type :: Hyp.val Term.nats .type :: Γ
            match inferType step_ctx s with
            | some (.expr .type s_ty) =>
                if s_ty == step_ty then some (.expr .type (C.subst0 e)) else none
            | _ => none
          else none
        | _ => none
      | _ => none
    | _ => none

  -- ── Not inferrable without annotation ────────────────────────────────────
  -- abort           : return type is arbitrary, no annotation in term
  -- inj b / disj b  : need the other branch type
  -- case / case_pr  : motive C not carried in the term
  -- let_bin forms   : motive C not carried in the term
  -- natrec prop     : requires Γ.upgrade (not implemented)
  -- ir forms        : equality proofs (trans, cong, prir, …)
  -- nz forms        : beta-reduction proofs
  | _ => none

end Untyped
