import Ambifine.Untyped
open Untyped

inductive HypKind
  | val (s: AnnotSort) -- Computational/Logical
  | gst -- Refinement
deriving DecidableEq, BEq, Repr

inductive Hyp where
| gst (ty : Term)
| type (ty : Term)
| prop (ty : Lean.Expr)
-- Destructure-derived: stores the source subset Term so the proof env can
-- introduce these as let-bindings to the projections, preserving the link to
-- the source.  `destructVal` is the value side; `destructProp` the proof side.
| destructVal (ty : Term) (src : Term)
| destructProp (ty : Lean.Expr) (src : Term)

abbrev Ctx := List Hyp

def Ctx.upgrade (Γ : Ctx) : Ctx := Γ.map fun h =>
  match h with
  | .gst ty => .type ty
  | e => e
