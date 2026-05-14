import Ambifine.Elab

#lang ERT

def does_it_check : 5 = 5 := by rfl
def another_prop : 5 ≤ 6 := by grind

def test : (a : {x : ℕ | x = 5}) → {x : ℕ | x = 5} :=
  λ a : {x : ℕ | x = 5} .
    let {x, p} : {x : ℕ | x = 5} = a in
    {5, by grind : 5 = 5} : {x : ℕ | x = 5}

def list_def : list ℕ := 3 :: 4 :: (nil : list ℕ)

def more_prop : ∃x : List Nat, x = list_def := by grind

def list_refine : (a : {x : list ℕ | x = list_def}) →
    {x : list ℕ | x = list_def} :=
  λ a : {x : list ℕ | x = list_def} .
    {3 :: 4 :: (nil : list ℕ),
      by grind : [3, 4] = list_def} : {x : list ℕ | x = list_def}

def length : (x : list ℕ) → ℕ :=
  λ x : list ℕ . listrec [(x : list ℕ) ↦ ℕ] x
    | 0
    | hd, tl, ih ↦ ((succ : (n : ℕ) → ℕ) ih)

def length_example : (length list_def) = 2 := by
  simp [length, list_def]
