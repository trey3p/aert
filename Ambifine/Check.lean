import Ambifine.Untyped
import Ambifine.Context
import Ambifine.Subst
import Ambifine.UntypedToExpr
import Ambifine.Infer
import Lean

open Lean Meta

namespace Check

def check (ρ : Env) (e : Untyped.Term) (T : Untyped.Annot) : Elab.TermElabM Unit := do
  let annot ← withCtxToLocalCtx' ρ [] [] (λ x ↦ Untyped.inferType [] ρ x e)
  match annot, T with
  | .exprType a, .exprType t =>
    -- Convert both to Lean Exprs and use `isDefEq`.  Structural BEq on
    -- `Annot` (which embeds `Lean.Expr` with hygienic binder names) is too
    -- strict — different elaborations produce different `mkFreshUserName`
    -- suffixes even when the types are the same up to alpha-equivalence.
    IO.eprintln s!"check: inferred Term = {repr a}"
    IO.eprintln s!"check: expected Term = {repr t}"
    let a_expr ← a.toExpr ρ []
    let t_expr ← t.toExpr ρ []
    unless ← isDefEq a_expr t_expr do
      throwError m!"Expected type is {repr T}, got {repr annot}"
  | _, _ =>
    if annot != T then
      throwError m!"Expected type is {repr T}, got {repr annot}"

end Check
