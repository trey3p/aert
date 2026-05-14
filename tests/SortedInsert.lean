import Ambifine.Elab

/-!
  Sortedness-preserving insertion.

  - `sorted` lives Lean-side: an inductive predicate, outside any decidable
    fragment.  Refinements mention it directly.
  - `insert` is implemented *in ambifine* via `listrec` + `cases` on a
    decidable comparison.  No mathlib fall-back for the algorithm.
  - The correctness obligations (`sorted (insert x xs)`,
    `length (insert x xs) = length xs + 1`) close by induction on `xs`
    paired with `grind` / `simp` discharging the leaves — the
    "proving + automation" combination.
-/

-- User-defined predicate.  Not in any SMT-decidable theory.
def sorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | x :: y :: r => x ≤ y ∧ sorted (y :: r)

-- Decidable ≤ on ℕ packaged as a coproduct so the ambifine `cases`
-- eliminator can split on it.  This is the one bridge to Lean: a small
-- helper that turns a decidable proposition into structural data.
def leDec (a b : Nat) : (a ≤ b) ∨ (b < a) :=
  if h : a ≤ b then .inl h else .inr (Nat.lt_of_not_le h)

#lang ERT

-- `insert x l`: insert `x` into a sorted list, preserving sortedness and
-- growing the length by one.  Refinements use `List.length` directly
-- (no ambifine-side `length` needed — it's the same function the listrec
-- elaborates to).
def insert :
    (x : ℕ) →
    (l : {l : list ℕ | sorted l}) →
    {l' : list ℕ | sorted l' ∧ List.length l' = List.length l + 1} :=
  λ x : ℕ .
  λ l : {l : list ℕ | sorted l} .
    let {xs, hs} : {l : list ℕ | sorted l} = l in
    -- Body: ordinary insertion-sort step, written in ambifine.
    --   nil           ↦ [x]
    --   hd :: tl, ih  ↦ case x ≤ hd of  inl _ ↦ x :: hd :: tl
    --                                    inr _ ↦ hd :: ih
    let result : list ℕ :=
      listrec [(_ : list ℕ) ↦ list ℕ] xs
        | x :: (nil : list ℕ)
        | hd, tl, ih ↦
            cases [_ : (x ≤ hd) + (hd < x) ↦ list ℕ] (leDec x hd)
              | inl (_ : (x ≤ hd)) ↦ x :: hd :: tl
              | inr (_ : (hd < x)) ↦ hd :: ih
    in
    -- Correctness.  The structure of each branch:  induction on `xs`,
    -- `grind` (or `simp` + `omega`) closing the leaves with the
    -- definitions of `sorted`, `insert`, and `leDec` as hints.
    {result,
      by
        refine ⟨?_, ?_⟩
        · -- sorted result
          induction xs with
          | nil => simp [sorted]
          | cons h t ih_xs =>
            -- Split on the comparison; both branches reduce to a fact
            -- about `sorted` of a 2-element prefix, plus `hs`.
            unfold leDec; split <;> grind [sorted]
        · -- List.length result = List.length xs + 1
          induction xs with
          | nil       => rfl
          | cons _ _ ih_xs =>
            unfold leDec; split <;> simp [List.length, ih_xs] <;> omega
      : sorted result ∧ List.length result = List.length xs + 1
    } : {l' : list ℕ | sorted l' ∧ List.length l' = List.length l + 1}
