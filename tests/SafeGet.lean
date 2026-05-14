import Ambifine.Elab

#lang ERT

-- Length of a list of naturals.
def length : (xs : list ℕ) → ℕ :=
  λ xs : list ℕ . listrec [(x : list ℕ) ↦ ℕ] xs
    | 0
    | hd, tl, ih ↦ ((succ : (n : ℕ) → ℕ) ih)

-- Addition on ℕ, by natrec on the first argument.
def plus : (m : ℕ) → (n : ℕ) → ℕ :=
  λ m : ℕ . λ n : ℕ .
    natrec [k ↦ ℕ] m
      | n
      | ‖succ p‖, ih ↦ ((succ : (n : ℕ) → ℕ) ih)

-- Multiplication on ℕ, by natrec on the first argument.
def mult : (m : ℕ) → (n : ℕ) → ℕ :=
  λ m : ℕ . λ n : ℕ .
    natrec [k ↦ ℕ] m
      | 0
      | ‖succ p‖, ih ↦
          (((plus : (a : ℕ) → (b : ℕ) → ℕ) n : (b : ℕ) → ℕ) ih)

-- Safe indexed access.  The refinement `i < length xs` is the precondition;
-- once it is satisfied at the call site, the implementation can never go
-- out of bounds.  Implemented by listrec on xs producing a function on i.
def get : (xs : list ℕ) → (i : {x : ℕ | x < length xs}) → ℕ :=
  λ xs : list ℕ .
    listrec [(ys : list ℕ) ↦ (i : {x : ℕ | x < length ys}) → ℕ] xs
      -- nil: precondition x < 0 is unsatisfiable, so this branch is dead.
      -- We extract the proof and let the refinement do the absurd-elimination.
      | λ i : {x : ℕ | x < 0} .
          let {x, p} : {x : ℕ | x < 0} = i in 0
      -- cons hd tl: at index 0 return hd, otherwise recurse on tl with i-1.
      | hd, tl, ih ↦ λ i : {x : ℕ | x < length (hd :: tl)} .
          let {idx, p} : {x : ℕ | x < length (hd :: tl)} = i in
          natrec [n ↦ ℕ] idx
            | hd
            | ‖succ j‖, ih ↦
                ((ih : (i : {x : ℕ | x < length tl}) → ℕ)
                  ({j, by grind : j < length tl} : {x : ℕ | x < length tl}))

-- flatIndex, restated with an explicit refinement witness in the body so the
-- typing obligation is local to this definition.
def flatIndex : (rows : {r : ℕ | r > 0})
              → (cols : {c : ℕ | c > 0})
              → (i : {x : ℕ | x < rows})
              → (j : {x : ℕ | x < cols})
              → {k : ℕ | k < mult rows cols} :=
  λ rows : {r : ℕ | r > 0} .
  λ cols : {c : ℕ | c > 0} .
  λ i : {x : ℕ | x < rows} .
  λ j : {x : ℕ | x < cols} .
    let {iv, pi} : {x : ℕ | x < rows}  = i in
    let {jv, pj} : {x : ℕ | x < cols}  = j in
    let {rv, pr} : {r : ℕ | r > 0}     = rows in
    let {cv, pc} : {c : ℕ | c > 0}     = cols in
    {(((plus : (a : ℕ) → (b : ℕ) → ℕ)
         (((mult : (a : ℕ) → (b : ℕ) → ℕ) iv : (b : ℕ) → ℕ) cv)
         : (b : ℕ) → ℕ) jv),
      by grind : plus (mult iv cv) jv < mult rv cv}
      : {k : ℕ | k < mult rows cols}

