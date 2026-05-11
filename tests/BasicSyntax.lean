import Ambifine.Elab

#lang ERT

def does_it_check : 5 =(ℕ) 5 := by rfl

def test : (a : {x : ℕ | x =(ℕ) 5}) → {x : ℕ | x =(ℕ) 5} :=
  λ a : {x : ℕ | x =(ℕ) 5} .
    let {x, p} : {x : ℕ | x =(ℕ) 5} = a in
    {5, by grind : 5 =(ℕ) 5} : {x : ℕ | x =(ℕ) 5}

def test2 : list ℕ := (3 : ℕ) :: (4 : ℕ) :: (nil : list ℕ)
