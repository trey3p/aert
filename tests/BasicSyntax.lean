import Ambifine.Elab

#lang ERT

def does_it_check : 5 = 5 := by rfl

def test : (a : {x : ℕ | x = 5}) → {x : ℕ | x = 5} :=
  λ a : {x : ℕ | x = 5} .
    let {x, p} : {x : ℕ | x = 5} = a in
    {5, by grind : x = 5}

def test2 : 𝟙 := test
