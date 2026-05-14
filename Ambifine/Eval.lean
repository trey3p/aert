import Ambifine.Untyped
import Ambifine.Subst
open Lean Meta
/-!
  Call-by-value operational semantics for `Untyped.Term`.

  Refinement types: they reduce only inside
  their non-binding subterms (or not at all).  All real computation is the
  usual β reduction for STLC extended with the structural recursors for
  ℕ and `List`.
-/

namespace Untyped

partial def eval (ρ : Env) : Term → MetaM Term
  -- ── Values: variables, embedded proofs, constants ────────────────────────
  | .var v       => return .var v
  | .proof e ty  => return .proof e ty
  | .const c     => (
      match c with
      | TermKind.definition n =>
        match ρ.find? (·.name == n) with
        | some s =>  (
          match s with
          | Statement.defn n ty tm => return tm
          | Statement.thm n ty pf => return .proof pf ty
        )
        | _ => throwError "Incorrect const typing"
      | _ => return .const c
    )

  -- ── Type formers (inert) ─────────────────────────────────────────────────
  | Term.pi A B        => return Term.pi A B
  | Term.sigma A B     => return  Term.sigma A B
  | Term.coprod A B    => return Term.coprod A B
  | Term.set A P       => return Term.set A P
  | Term.assume φ A    => return Term.assume φ A
  | Term.intersect A B => return Term.intersect A B
  | Term.union A B     => return Term.union A B
  | Term.list A        => return Term.list A

  -- ── λ-abstractions are values; do not reduce under binders ───────────────
  | Term.lam A t       => return Term.lam A t
  | Term.lam_pr φ t    => return Term.lam_pr φ t
  | Term.lam_irrel A t => return Term.lam_irrel A t

  -- ── Data constructors: evaluate components ───────────────────────────────
  | Term.pair l r    => do
      let a ← (eval ρ l)
      let b ← (eval ρ r)
      return Term.pair a b
  | Term.repr l r    => do
      let a ← (eval ρ l)
      let b ← (eval ρ r)
      return Term.repr (a) (b)
  | Term.elem x p A  => do
      let a ← (eval ρ x)
      return Term.elem (a) p A
  | Term.inj b A t   => do
      let a ← (eval ρ t)
      return Term.inj b A a
  | Term.em A        => return Term.em A
  | Term.cons x xs   => do
      let a ← (eval ρ x)
      let b ← (eval ρ xs)
      return Term.cons a b

  -- ── β-reduction: function / proof / irrelevant application ───────────────
  | Term.app A f x => do
      let xv ← eval ρ x
      let y  ← eval ρ f
        match y with
        | Term.lam _ body =>
          let a ← (body.subst0 xv)
          eval ρ a
        | fv              => return Term.app A fv xv
  | Term.app_pr A f p => do
    let a ← eval ρ f
      match a with
      | Term.lam_pr _ body =>
        let y ← (body.subst0 p)
        eval ρ y
      | fv                 => return Term.app_pr A fv p
  | Term.app_irrel A f x => do
    let a ← eval ρ f
      match a with
      | Term.lam_irrel _ body =>
        let b ← (body.subst0 x)
        eval ρ b
      | fv                    => return Term.app_irrel A fv x

  -- ── Σ / set / union elimination ──────────────────────────────────────────
  | Term.let_pair k P e e' => do
    let a ← eval ρ e
    match a with
    | Term.pair l r =>
      let e'' ← (e'.subst0 r)
      let e''' ← e''.subst0 l
      eval ρ e'''
    | ev            => return Term.let_pair k P ev e'
  | Term.let_set k P e e' => do
    let a ← eval ρ e
    match a with
    | Term.elem x p _ =>
      let e'' ← (e'.subst0 p)
      let e''' ← e''.subst0 x
      eval ρ e'''
    | ev              => return Term.let_set k P ev e'
  | Term.let_repr k P e e' => do
    let a ← eval ρ e
    match a with
    | Term.repr l r =>
      let e'' ← e'.subst0 r
      let e''' ← e''.subst0 l
      eval ρ e'''
    | ev            => return Term.let_repr k P ev e'

  -- ── Coproduct elimination ────────────────────────────────────────────────
  | Term.case k K d l r => do
    let a ← eval ρ d
    match a with
    | Term.inj 0 _ x =>
      let l' ← l.subst0 x
      eval ρ l'
    | Term.inj 1 _ x =>
      let r' ← r.subst0 x
      eval ρ r'
    | dv             => return Term.case k K dv l r

  -- ── ℕ recursion: zero ↦ z;  succ n ↦ s[natrec(n) / 0][n / 0] ─────────────
  | Term.natrec k K e z s => do
    let e' ← eval ρ e
    match e' with
    | Term.zero => eval ρ z
    | Term.app _ Term.succ n =>
      let ih := Term.natrec k K n z s
      let s' ← s.subst0 ih
      let s'' ← s'.subst0 n
      eval ρ s'
    | ev => return Term.natrec k K ev z s

  -- ── List recursion ───────────────────────────────────────────────────────
  -- em A ↦ nil_case
  -- cons x xs ↦ cons_case[ih/0][xs/0][x/0]
  --   where cons_case has 3 binders, var 0 = ih, var 1 = tail, var 2 = head
  | Term.listrec k K e nil_case cons_case => do
    let e' ← eval ρ e
    match e' with
    | Term.em _ => eval ρ nil_case
    | Term.cons x xs =>
      let ih := Term.listrec k K xs nil_case cons_case
      let cons' ← cons_case.subst0 ih
      let cons'' ← cons'.subst0 x
      eval ρ cons''
    | ev => return Term.listrec k K ev nil_case cons_case

  -- ── Anything else (ir / beta_zero / beta_succ / let_bin_beta / …) ────────
  -- These are propositional witnesses or stuck open terms; return as-is.
  | t => return t

end Untyped
