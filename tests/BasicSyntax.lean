import Ambifine.Elab

#lang ERT

def test : { x : ℕ | x = 5} := {5, by simp : 7 = 7}
