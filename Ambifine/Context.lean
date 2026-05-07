import Ambifine.Untyped
open Untyped

inductive HypKind
  | val (s: AnnotSort) -- Computational/Logical
  | gst -- Refinement
deriving DecidableEq, BEq

structure Hyp where
  ty : Term
  kind : HypKind

abbrev Hyp.val (A: Term) (s: AnnotSort) := Hyp.mk A (HypKind.val s)
abbrev Hyp.gst (A: Term) := Hyp.mk A HypKind.gst

def Ctx := List Hyp

-- Make every binding ghost (computationally irrelevant).
-- Used for checking terms in ghost positions (irrelevant arguments, union witnesses, etc.).
def Ctx.upgrade (Γ : Ctx) : Ctx := Γ.map fun h => Hyp.gst h.ty
