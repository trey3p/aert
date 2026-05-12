import Ambifine.Untyped
import Ambifine.Subst

/-!
  Call-by-value operational semantics for `Untyped.Term`.

  Refinement types and propositions are inert: they reduce only inside
  their non-binding subterms (or not at all).  All real computation is the
  usual β/ι reduction for STLC extended with the structural recursors for
  ℕ and `List`.
-/

namespace Untyped

partial def eval : Term → Term
  -- ── Values: variables, embedded proofs, constants ────────────────────────
  | .var v       => .var v
  | .proof e ty  => .proof e ty
  | .const c     => .const c

  -- ── Type formers (inert) ─────────────────────────────────────────────────
  | Term.pi A B        => Term.pi A B
  | Term.sigma A B     => Term.sigma A B
  | Term.coprod A B    => Term.coprod A B
  | Term.set A P       => Term.set A P
  | Term.assume φ A    => Term.assume φ A
  | Term.intersect A B => Term.intersect A B
  | Term.union A B     => Term.union A B
  | Term.list A        => Term.list A

  -- ── Proposition formers (inert) ──────────────────────────────────────────
  | Term.dand φ ψ     => Term.dand φ ψ
  | Term.dimplies φ ψ => Term.dimplies φ ψ
  | Term.or φ ψ       => Term.or φ ψ
  | Term.forall_ A φ  => Term.forall_ A φ
  | Term.exists_ A φ  => Term.exists_ A φ
  | Term.eq A l r     => Term.eq A l r

  -- ── λ-abstractions are values; do not reduce under binders ───────────────
  | Term.lam A t       => Term.lam A t
  | Term.lam_pr φ t    => Term.lam_pr φ t
  | Term.lam_irrel A t => Term.lam_irrel A t

  -- ── Data constructors: evaluate components ───────────────────────────────
  | Term.pair l r    => Term.pair (eval l) (eval r)
  | Term.repr l r    => Term.repr (eval l) (eval r)
  | Term.elem x p A  => Term.elem (eval x) p A
  | Term.inj b A t   => Term.inj b A (eval t)
  | Term.em A        => Term.em A
  | Term.cons x xs   => Term.cons (eval x) (eval xs)

  -- ── β-reduction: function / proof / irrelevant application ───────────────
  | Term.app A f x =>
    let xv := eval x
    match eval f with
    | Term.lam _ body => eval (body.subst0 xv)
    | fv              => Term.app A fv xv
  | Term.app_pr A f p =>
    match eval f with
    | Term.lam_pr _ body => eval (body.subst0 p)
    | fv                 => Term.app_pr A fv p
  | Term.app_irrel A f x =>
    match eval f with
    | Term.lam_irrel _ body => eval (body.subst0 x)
    | fv                    => Term.app_irrel A fv x

  -- ── Σ / set / union elimination ──────────────────────────────────────────
  | Term.let_pair k P e e' =>
    match eval e with
    | Term.pair l r => eval ((e'.subst0 r).subst0 l)
    | ev            => Term.let_pair k P ev e'
  | Term.let_set k P e e' =>
    match eval e with
    | Term.elem x p _ => eval ((e'.subst0 p).subst0 x)
    | ev              => Term.let_set k P ev e'
  | Term.let_repr k P e e' =>
    match eval e with
    | Term.repr l r => eval ((e'.subst0 r).subst0 l)
    | ev            => Term.let_repr k P ev e'

  -- ── Coproduct elimination ────────────────────────────────────────────────
  | Term.case k K d l r =>
    match eval d with
    | Term.inj 0 _ x => eval (l.subst0 x)
    | Term.inj 1 _ x => eval (r.subst0 x)
    | dv             => Term.case k K dv l r

  -- ── ℕ recursion: zero ↦ z;  succ n ↦ s[natrec(n) / 0][n / 0] ─────────────
  | Term.natrec k K e z s =>
    match eval e with
    | Term.zero => eval z
    | Term.app _ Term.succ n =>
      let ih := Term.natrec k K n z s
      eval ((s.subst0 ih).subst0 n)
    | ev => Term.natrec k K ev z s

  -- ── List recursion: em ↦ nil_case;  cons x xs ↦ c[listrec(xs) / 0][x / 0] -
  | Term.listrec k K e nil_case cons_case =>
    match eval e with
    | Term.em _ => eval nil_case
    | Term.cons x xs =>
      let ih := Term.listrec k K xs nil_case cons_case
      eval ((cons_case.subst0 ih).subst0 x)
    | ev => Term.listrec k K ev nil_case cons_case

  -- ── Anything else (ir / beta_zero / beta_succ / let_bin_beta / …) ────────
  -- These are propositional witnesses or stuck open terms; return as-is.
  | t => t

end Untyped
