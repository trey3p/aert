import Lean

/-!
  Untyped terms of Lambda_ert, copied from old-ert repo.
-/

namespace Untyped

inductive AnnotSort
  | type
  | prop
  deriving DecidableEq, BEq, Repr

-- Term kinds
--TODO: consider making higher order?
inductive TermKind: List Nat -> Type
  -- Types
  | unit: TermKind []
  | pi: TermKind [0, 1] -- (pi, type, type)
  | sigma: TermKind [0,1] -- (sigma, type, type)
  | coprod: TermKind [0, 0]
  --TODO: consider merging with (pi, prop, type)
  | assume: TermKind [0, 1]
  --TODO: consider merging with (sigma, prop, type)
  | set: TermKind [0, 1]
  --TODO: consider merging with (pi, ghost, type)
  | intersect: TermKind [0, 1]
  --TODO: consider merging with (sigma, ghost, type)
  | union: TermKind [0, 1]

  -- Propositions
  | top: TermKind []
  | bot: TermKind []
  --TODO: consider merging with (pi, prop, prop)
  | dimplies: TermKind [0, 1]
  --TODO: consider dependent and, analogous to (sigma, prop, prop)
  | dand: TermKind [0, 1]
  | or: TermKind [0, 0]
  --TODO: consider merging with (pi, type, prop) == (pi, ghost, prop)
  | forall_: TermKind [0, 1]
  --TODO: consider merging with (sigma, type, prop) == (sigma, ghost, prop)
  | exists_: TermKind [0, 1]

  -- Terms
  | nil: TermKind []
  -- Consider merging with intro/elim for (pi, type, type)
  | lam: TermKind [0, 1]
  | app: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, type, type)
  | pair: TermKind [0, 0]
  | let_pair: AnnotSort -> TermKind [0, 0, 2]
  | inj (b: Fin 2): TermKind [0]
  | case: AnnotSort -> TermKind [0, 0, 1, 1]
  -- Consider merging with intro/elim for (pi, type, prop)
  | lam_pr: TermKind [0, 1]
  | app_pr: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, type, prop)
  | elem: TermKind [0, 0]
  | let_set: AnnotSort -> TermKind [0, 0, 2]
  -- Consider merging with intro/elim for (pi, ghost, type)
  | lam_irrel: TermKind [0, 1]
  | app_irrel: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, ghost, type)
  | repr: TermKind [0, 0]
  | let_repr: AnnotSort -> TermKind [0, 0, 2]

  -- Natural numbers
  | nats: TermKind []
  | zero: TermKind []
  | succ: TermKind []
  | natrec: AnnotSort -> TermKind [1, 0, 0, 2]
  | beta_zero: TermKind [1, 0, 2]
  | beta_succ: TermKind [1, 0, 0, 2]
deriving BEq, Repr

inductive Term: Type
  | var (v: Nat)
  | proof (e : Lean.Expr) (ty : Term)
  | const (c: TermKind [])
  | unary (k: TermKind [0]) (t: Term)
  | let_bin (k: TermKind [0, 0, 2]) (P: Term) (e: Term) (e': Term)
  | let_bin_beta (k: TermKind [0, 0, 0, 2]) (P: Term) (l r: Term) (e': Term)
  | bin (k: TermKind [0, 0]) (l: Term) (r: Term)
  | abs (k: TermKind [0, 1]) (A: Term) (t: Term)
  | tri (k: TermKind [0, 0, 0]) (A: Term) (l: Term) (r: Term)
  | ir (k: TermKind [0, 0, 1]) (x: Term) (y: Term) (P: Term)
  | cases (k: TermKind [0, 0, 1, 1]) (K: Term) (d: Term) (l: Term) (r: Term)
  | nr (k: TermKind [1, 0, 0, 2]) (K: Term) (e: Term) (z: Term) (s: Term)
  | nz (k: TermKind [1, 0, 2]) (K: Term) (z: Term) (s: Term)
deriving BEq, Repr

-- Types
abbrev Term.unit := const TermKind.unit
abbrev Term.nats := const TermKind.nats
abbrev Term.pi := abs TermKind.pi
abbrev Term.sigma := abs TermKind.sigma
abbrev Term.coprod := bin TermKind.coprod
abbrev Term.set := abs TermKind.set
abbrev Term.assume := abs TermKind.assume
abbrev Term.intersect := abs TermKind.intersect
abbrev Term.union := abs TermKind.union

-- Propositions
abbrev Term.top := const TermKind.top
abbrev Term.bot := const TermKind.bot
abbrev Term.dand := abs TermKind.dand
abbrev Term.or := bin TermKind.or
abbrev Term.dimplies := abs TermKind.dimplies
abbrev Term.forall_ := abs TermKind.forall_
abbrev Term.exists_ := abs TermKind.exists_
abbrev Term.eq := tri TermKind.eq

-- Terms
abbrev Term.nil := const TermKind.nil
abbrev Term.lam := abs TermKind.lam
@[match_pattern]
abbrev Term.app := tri TermKind.app
abbrev Term.pair := bin TermKind.pair
abbrev Term.let_pair := λk => let_bin (TermKind.let_pair k)
abbrev Term.inj := λb => unary (TermKind.inj b)
abbrev Term.case := λk => cases (TermKind.case k)
abbrev Term.elem := bin TermKind.elem
abbrev Term.let_set := λk => let_bin (TermKind.let_set k)
abbrev Term.lam_pr := abs TermKind.lam_pr
abbrev Term.app_pr := tri TermKind.app_pr
abbrev Term.lam_irrel := abs TermKind.lam_irrel
abbrev Term.app_irrel := tri TermKind.app_irrel
abbrev Term.repr := bin TermKind.repr
abbrev Term.let_repr := λk => let_bin (TermKind.let_repr k)

-- Natural numbers
abbrev Term.zero := const TermKind.zero
abbrev Term.succ := const TermKind.succ
abbrev Term.natrec (k) := nr (TermKind.natrec k)
abbrev Term.beta_zero := nz TermKind.beta_zero
abbrev Term.beta_succ := nr TermKind.beta_succ

end Untyped
