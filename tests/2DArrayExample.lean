import Ambifine.Elab

#lang ERT

def flatIndex : (rows : {r : ℕ | r > 0})
                → (cols : {c : ℕ | c > 0})
                → (i : {x : ℕ | x < rows})
                → (j : {x : ℕ | x < cols})
                → {k : ℕ  | k < rows * cols}
          :=
                λ (rows : {r : ℕ | r > 0}).
                λ (cols : {c : ℕ | c > 0}).
                λ (i : {x : ℕ | x < rows}).
                λ (j : {x : ℕ  | x < cols}). cols i j = i * cols + j
