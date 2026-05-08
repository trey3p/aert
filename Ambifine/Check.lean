import Ambifine.Untyped
import Ambifine.Context
import Ambifine.Subst
import Ambifine.UntypedToExpr
import Ambifine.Infer
import Lean

open Lean Meta

namespace Check

-- This is not fully implemented.
def check (Γ : Ctx) (ρ : Env) (e : Untyped.Term) (T : Untyped.Annot) : Elab.TermElabM Bool := do
  withCtxToLocalCtx' ρ Γ [] (λ x ↦ Untyped.inferType Γ ρ x e) >>= fun inferred =>
    match inferred with
    | some annot => return (annot == T)
    | none => return false

end Check
