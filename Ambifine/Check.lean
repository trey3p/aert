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
  if annot != T then
    throwError m!"Expected type is {repr T}, got {repr annot}"

end Check
