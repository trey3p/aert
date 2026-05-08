import Ambifine.Untyped
open Untyped

inductive HypKind
  | val (s: AnnotSort) -- Computational/Logical
  | gst -- Refinement
deriving DecidableEq, BEq, Repr

structure Hyp where
  ty : Term
  kind : HypKind
deriving Repr

abbrev Hyp.val (A: Term) (s: AnnotSort) := Hyp.mk A (HypKind.val s)
abbrev Hyp.gst (A: Term) := Hyp.mk A HypKind.gst

abbrev Ctx := List Hyp

-- Make every binding ghost a val.
def Ctx.upgrade (Γ : Ctx) : Ctx := Γ.map fun h => Hyp.val h.ty (AnnotSort.type)
