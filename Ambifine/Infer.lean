import Ambifine.Untyped
import Ambifine.Context

-- Mirrors old-ert's Annot: distinguishes "e is a type/prop" from "e has type A"
inductive Annot where
  | sort : AnnotSort → Annot
  | expr : AnnotSort → Term → Annot

-- Shift all free variables with index ≥ cutoff up by shift.
-- The binding depth encoded in each TermKind index determines how much
-- the cutoff grows as lift descends under binders.
def Term.lift (cutoff shift : Nat) : Term → Term
  | .var v             => .var (if v < cutoff then v else v + shift)
  | .const c           => .const c
  | .unary k t         => .unary k (t.lift cutoff shift)
  | .bin k l r         => .bin k (l.lift cutoff shift) (r.lift cutoff shift)
  | .abs k A t         => .abs k (A.lift cutoff shift) (t.lift (cutoff + 1) shift)
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

def Term.wk1 (t : Term) : Term := t.lift 0 1
def Term.wkn (n : Nat) (t : Term) : Term := t.lift 0 n

-- Computable analogue of HasVar: walk the context, applying wk1 at each step
-- so the returned type is valid in the full context (not just the tail).
def lookupVar : Context → Nat → Option (HypKind × Term)
  | [],     _     => none
  | h :: _, 0     => some (h.kind, h.ty.wk1)
  | _ :: Γ, n + 1 => lookupVar Γ n |>.map (fun (k, A) => (k, A.wk1))

-- inferType mirrors HasType as a decision procedure.
-- Limitations vs the full HasType relation:
--   - Cases whose result type requires substitution (app, eliminations,
--     natrec, equality terms) return none until subst is implemented.
--   - Context upgrade (Γ.upgrade) for ghost/irrelevance is not applied.
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

  -- ── Needs substitution or context upgrade ─────────────────────────────────
  -- app, app_pr, app_irrel         : result is B.subst0 r
  -- pair, elem, repr, wit, dconj   : checking requires subst
  -- let_bin, let_bin_beta, cases   : eliminations, result needs subst
  -- nr (natrec), nz                : result is C.subst0 e
  -- unary (abort, refl, inj, disj) : abort needs annotation; others need subst/upgrade
  -- ir (cong, trans, prir, …)      : equality terms
  | _ => none
