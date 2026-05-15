import Lean

open Lean Elab Tactic Meta

namespace Ambifine

/-- True when `e` mentions a multiplication subterm anywhere.  We look for
    `HMul.hMul`, `Mul.mul`, `Nat.mul`, and any constant literally named
    `mult` (the ambifine multiplication). -/
partial def containsMul (e : Expr) : Bool :=
  if e.isAppOf ``HMul.hMul then true
  else if e.isAppOf ``Mul.mul then true
  else if e.isAppOf ``Nat.mul then true
  else
    match e with
    | .const n _ => n.toString = "mult"
    | .app f a => containsMul f || containsMul a
    | .lam _ d b _ => containsMul d || containsMul b
    | .forallE _ d b _ => containsMul d || containsMul b
    | .letE _ t v b _ => containsMul t || containsMul v || containsMul b
    | .mdata _ b => containsMul b
    | .proj _ _ b => containsMul b
    | _ => false

/-- Collect every distinct multiplication subterm appearing in `e` into `acc`.
    Only fully-applied mult expressions are collected — partial applications
    like `HMul.hMul iv` would not type-check on their own. -/
partial def collectMul (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let isMul :=
    e.isAppOfArity ``HMul.hMul 6 ||
    e.isAppOfArity ``Mul.mul 4 ||
    e.isAppOfArity ``Nat.mul 2
  -- Filter out subterms with loose bvars (e.g. mult inside a ∀-body); we can't
  -- generalize over those.
  let acc :=
    if isMul && !e.hasLooseBVars && !acc.any (· == e) then acc.push e else acc
  match e with
  | .app f a => collectMul a (collectMul f acc)
  | .lam _ d b _ => collectMul b (collectMul d acc)
  | .forallE _ d b _ => collectMul b (collectMul d acc)
  | .letE _ t v b _ => collectMul b (collectMul v (collectMul t acc))
  | .mdata _ b => collectMul b acc
  | .proj _ _ b => collectMul b acc
  | _ => acc

/-- Collect all mult subterms appearing in the goal AND in any propositional
    hypothesis of `g`.  Goal terms come first; hypothesis terms are appended
    only if they're not already in the accumulator. -/
def collectMulFromContext (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  let mut acc := collectMul target
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let t ← instantiateMVars ldecl.type
    if ← Meta.isProp t then
      acc := collectMul t acc
  return acc

/-- Repeatedly split conjunctions in the current goal, returning the list of
    leaf goals (each of which is no longer an `And`). -/
partial def splitAnds : TacticM Unit := do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for g in goals do
    let target ← instantiateMVars (← g.getType)
    if target.isAppOfArity ``And 2 then
      let subs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      setGoals subs
      splitAnds
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals.concat g
  setGoals newGoals

/-- Try to close the single goal `g` by running `grind` directly.  Returns
    whether grind closed it; on failure, restores the saved state. -/
def tryGrind (g : MVarId) : TacticM Bool := do
  let state ← saveState
  setGoals [g]
  try
    evalTactic (← `(tactic| grind))
    if (← getGoals).isEmpty then return true
    state.restore; return false
  catch _ => state.restore; return false

/-- Try to close `g` by abstracting every mult subterm (in goal and hypotheses)
    to a fresh variable, then running `grind`.  On failure, restores state. -/
def tryAbstractAndGrind (g : MVarId) : TacticM Bool := do
  let state ← saveState
  setGoals [g]
  try
    let muls ← collectMulFromContext g
    if muls.isEmpty then state.restore; return false
    -- Abstract via revert/generalize/intro so the substitution lands in
    -- hypotheses too.  This bypasses the syntax-roundtripping path that
    -- `generalize ... at *` would take and so works inside `#lang ERT`-style
    -- elaboration contexts where pretty-printed names need not roundtrip.
    let hypFVars ← g.withContext do
      let mut hs := #[]
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        let t ← instantiateMVars ldecl.type
        if ← Meta.isProp t then
          hs := hs.push ldecl.fvarId
      return hs
    let (_, g1) ← g.revert hypFVars
    let args : Array Lean.Meta.GeneralizeArg := muls.zipIdx.map fun (m, i) =>
      { expr := m, xName? := some (Name.mkSimple s!"_decidable_reduce_v_{i}"), hName? := none }
    let (_, g2) ← g1.generalize args
    let (_, g3) ← g2.introNP hypFVars.size
    setGoals [g3]
    evalTactic (← `(tactic| grind))
    if (← getGoals).isEmpty then return true
    state.restore; return false
  catch _ => state.restore; return false

/-- The core of `decidable_reduce`: split conjunctions; for each resulting atom,
    try `grind` first.  If the atom contains multiplication and `grind` failed,
    also try abstracting every mult subterm in the goal and hypotheses to a
    fresh variable then running `grind` (so the abstracted goal lives in
    Presburger).  Any atom not closed this way is left as a user-facing
    subgoal. -/
elab "decidable_reduce_core" : tactic => withMainContext do
  splitAnds
  let goals ← getGoals
  let mut remaining : List MVarId := []
  for g in goals do
    let target ← instantiateMVars (← g.getType)
    let hasMul := containsMul target
    let closed ←
      if hasMul then
        tryAbstractAndGrind g
      else
        tryGrind g
    unless closed do
      remaining := remaining.concat g
  setGoals remaining

/-- Tactic-level `decidable_reduce`: invokes `decidable_reduce_core` then runs
    any extra tactics. -/
syntax "decidable_reduce" (ppSpace tacticSeq)? : tactic

macro_rules
  | `(tactic| decidable_reduce) => `(tactic| decidable_reduce_core)
  | `(tactic| decidable_reduce $t:tacticSeq) =>
      `(tactic| decidable_reduce_core; ($t:tacticSeq))

/-- Term-level `decidable_reduce`: drop-in replacement for `by` that first
    invokes `decidable_reduce_core` (split + discharge linear atoms), then runs
    any additional tactics the user supplied. -/
syntax (name := decidableReduceTerm) "decidable_reduce " tacticSeq : term
syntax (name := decidableReduceTerm0) "decidable_reduce" : term

macro_rules
  | `(term| decidable_reduce) => `(term| by decidable_reduce_core)
  | `(term| decidable_reduce $t:tacticSeq) =>
      `(term| by decidable_reduce_core; ($t:tacticSeq))

end Ambifine
