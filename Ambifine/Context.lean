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

abbrev Ctx := List Hyp

def Ctx.upgrade (Γ : Ctx) : Ctx := Γ.map fun h =>
  match h with
  | .gst ty => .type ty
  | e => e
