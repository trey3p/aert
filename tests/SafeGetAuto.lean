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
-- Safe indexed access.  We dispatch on the index `idx` via natrec with a
-- dependent motive.  The motive `n ↦ (ys : list ℕ) → {x : ℕ | n < length ys} → ℕ`
-- abstracts over both the list to be indexed AND the proof that `n` fits.
-- Because the predecessor `j` of `succ j` is ghost in the ERT natrec, we
-- never reference `j` as a value; it only appears in the refinement
-- predicates the recursive call consumes.  The dummy `0` in each subset
-- constructor occupies the irrelevant value slot — only the proof matters.
def get : (xs : list ℕ) → (i : {x : ℕ | x < List.length xs}) → ℕ :=
  λ xs : list ℕ .
  λ i : {x : ℕ | x < List.length xs} .
    let {idx, p} : {x : ℕ | x < List.length xs} = i in
    (((natrec
        [n ↦ (ys : list ℕ) → (q : {x : ℕ | n < List.length ys}) → ℕ]
        idx
        -- BASE: n = 0.  Receive ys and a proof q that 0 < length ys, then
        -- listrec on ys.  The nil branch is unreachable but we return 0.
        | λ ys : list ℕ .
            λ q : {x : ℕ | 0 < List.length ys} .
              let {qv, pq} : {x : ℕ | 0 < List.length ys} = q in
              listrec [(zs : list ℕ) ↦ ℕ] ys
                | 0
                | hd, tl, _ih ↦ hd
        -- STEP: n = succ j.  IH `_rec : (ys : list ℕ) → {x | j < length ys} → ℕ`.
        -- Inner listrec on ys uses a *dependent* motive so the cons branch
        -- knows length zs = length tl + 1, enabling the proof discharge.
        | ‖succ j‖, _rec ↦
            λ ys : list ℕ .
            λ q : {x : ℕ | j + 1 < List.length ys} .
              (((listrec
                  [(zs : list ℕ) ↦ (q' : {x : ℕ | j + 1 < List.length zs}) → ℕ]
                  ys
                  -- nil branch: take q', destructure, ignore (unreachable).
                  | λ q' : {x : ℕ | j + 1 < List.length ([] : List Nat)} .
                      let {qv', pq'} : {x : ℕ | j + 1 < List.length ([] : List Nat)} = q' in 0
                  -- cons branch: peel hd, call _rec on tl.  From
                  -- q' : j + 1 < length (hd :: tl) = length tl + 1 we get
                  -- j < length tl.
                  | hd, tl, _ih ↦
                      λ q' : {x : ℕ | j + 1 < List.length (hd :: tl)} .
                        let {qv', pq'} : {x : ℕ | j + 1 < List.length (hd :: tl)} = q' in
                        (((_rec : (ys : list ℕ) → (q : {x : ℕ | j < List.length ys}) → ℕ) tl
                            : (q : {x : ℕ | j < List.length tl}) → ℕ)
                          ({0, by
                              have h : List.length (hd :: tl) = List.length tl + 1 := rfl
                              omega : j < List.length tl}
                            : {x : ℕ | j < List.length tl}))
                ) : (q' : {x : ℕ | j + 1 < List.length ys}) → ℕ) q)
      ) : (ys : list ℕ) → (q : {x : ℕ | idx < List.length ys}) → ℕ) xs
        : (q : {x : ℕ | idx < List.length xs}) → ℕ)
      ({0, p : idx < List.length xs} : {x : ℕ | idx < List.length xs})

-- flatIndex, restated with an explicit refinement witness in the body so the
-- typing obligation is local to this definition.
def flatIndex : (rows : {r : ℕ | r > 0})
              → (cols : {c : ℕ | c > 0})
              → (i : {x : ℕ | x < rows})
              → (j : {x : ℕ | x < cols})
              → {k : ℕ | k < rows * cols} :=
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
      by grind : (iv * cv) + jv < rv * cv}
      : {k : ℕ | k < rows * cols}

-- The payoff.  `flatIndex` produces a value with refinement `< mult rows cols`.
-- `arr` carries refinement `length arr = mult rows cols`.  Together these say
-- `flatIndex rows cols i j < length arr` — exactly `get`'s precondition.
-- No new arithmetic proof is needed at the call site; the refinements
-- compose mechanically.
def get2D : (rows : {r : ℕ | r > 0})
          → (cols : {c : ℕ | c > 0})
          → (arr : {a : list ℕ | length a = mult rows cols})
          → (i : {x : ℕ | x < rows})
          → (j : {x : ℕ | x < cols})
          → ℕ :=
  λ rows : {r : ℕ | r > 0} .
  λ cols : {c : ℕ | c > 0} .
  λ arr  : {a : list ℕ | length a = mult rows cols} .
  λ i    : {x : ℕ | x < rows} .
  λ j    : {x : ℕ | x < cols} .
    let {a,  eqL} : {a : list ℕ | length a = mult rows cols} = arr in
    let {k,  pk}  : {k : ℕ | k < mult rows cols} =
      ((((flatIndex
            : (rows : {r : ℕ | r > 0})
            → (cols : {c : ℕ | c > 0})
            → (i : {x : ℕ | x < rows})
            → (j : {x : ℕ | x < cols})
            → {k : ℕ | k < mult rows cols}) rows
            : (cols : {c : ℕ | c > 0})
            → (i : {x : ℕ | x < rows})
            → (j : {x : ℕ | x < cols})
            → {k : ℕ | k < mult rows cols}) cols
            : (i : {x : ℕ | x < rows})
            → (j : {x : ℕ | x < cols})
            → {k : ℕ | k < mult rows cols}) i
            : (j : {x : ℕ | x < cols})
            → {k : ℕ | k < mult rows cols}) j
    in
    (((get : (xs : list ℕ) → (i : {x : ℕ | x < length xs}) → ℕ) a
        : (i : {x : ℕ | x < length a}) → ℕ)
      ({k, by grind : k < length a} : {x : ℕ | x < length a}))
