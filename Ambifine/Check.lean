import Ambifine.Untyped
import Ambifine.Context
import Ambifine.Subst
import Ambifine.UntypedToExpr
import Ambifine.Infer
import Lean

open Lean Meta

namespace Check

def check (ρ : Env) (e : Untyped.Term) (T : Untyped.Annot) : Elab.TermElabM Bool := do
  let inferred ← withCtxToLocalCtx' ρ [] [] (λ x ↦ Untyped.inferType [] ρ x e)
  match inferred with
  | some annot => return (annot == T)
  | none => return false

end Check
