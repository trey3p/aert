import Ambifine.Elab

#lang ERT

def test : (a : {x : ℕ | x = 5}) → {x : ℕ | x = 5} :=
  λ a : {x : ℕ | x = 5} .
    let {x, p} : {x : ℕ | x = 5} = a in
    {5, by grind : x = 5}
