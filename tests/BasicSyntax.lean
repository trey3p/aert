import Ambifine.Elab

#lang ERT

def does_it_check : 5 =(ℕ) 5 := by rfl

def test : (a : {x : ℕ | x =(ℕ) 5}) → {x : ℕ | x =(ℕ) 5} :=
  λ a : {x : ℕ | x =(ℕ) 5} .
    let {x, p} : {x : ℕ | x =(ℕ) 5} = a in
    {5, by grind : 5 =(ℕ) 5} : {x : ℕ | x =(ℕ) 5}

def list_def : list ℕ := 3 :: 4 :: (nil : list ℕ)

def list_refine : (a : {x : list ℕ | x =(list ℕ) list_def}) →
    {x : list ℕ | x =(list ℕ) list_def} :=
  λ a : {x : list ℕ | x =(list ℕ) list_def} .
    {3 :: 4 :: (nil : list ℕ),
      by grind : (3 :: 4 :: (nil : list ℕ) =(list ℕ) list_def)} : {x : list ℕ | x =(list ℕ) list_def}

def list_length : (x : list ℕ) → ℕ :=
  λ x : list ℕ . listrec [(x : list ℕ) ↦ ℕ] x
    | 0
    | rest, ih ↦ (succ ih)
