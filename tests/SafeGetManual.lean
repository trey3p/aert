import Ambifine.Elab
import Ambifine.Tactics

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

def plus_eq : ∀ a b : Nat, plus a b = a + b := by
  intro a b
  induction a with
  | zero => show b = 0 + b; omega
  | «succ» a ih =>
    show plus a b + 1 = a + 1 + b
    rw [ih]; omega

-- Multiplication on ℕ, by natrec on the first argument.
def mult : (m : ℕ) → (n : ℕ) → ℕ :=
  λ m : ℕ . λ n : ℕ .
    natrec [k ↦ ℕ] m
      | 0
      | ‖succ p‖, ih ↦
          (((plus : (a : ℕ) → (b : ℕ) → ℕ) n : (b : ℕ) → ℕ) ih)

def mult_eq : ∀ a b : Nat, mult a b = a * b := by
  intro a b
  induction a with
  | zero => show (0 : Nat) = 0 * b; omega
  | «succ» a ih =>
    show plus b (mult a b) = (a + 1) * b
    rw [plus_eq, ih, Nat.succ_mul]; omega

-- Safe indexed access.  We dispatch on the index `idx` via natrec with a
-- dependent motive.  The motive `n ↦ (ys : list ℕ) → {x : ℕ | n < length ys} → ℕ`
-- abstracts over both the list to be indexed AND the proof that `n` fits.
-- Because the predecessor `j` of `succ j` is ghost in the ERT natrec, we
-- never reference `j` as a value; it only appears in the refinement
-- predicates the recursive call consumes.  The dummy `0` in each subset
-- constructor occupies the irrelevant value slot — only the proof matters.
def get : (xs : list ℕ) → (i : {x : ℕ | x < length xs}) → ℕ :=
  λ xs : list ℕ .
  λ i : {x : ℕ | x < length xs} .
    let {idx, p} : {x : ℕ | x < length xs} = i in
    (((natrec
        [n ↦ (ys : list ℕ) → (q : {x : ℕ | n < length ys}) → ℕ]
        idx
        -- BASE: n = 0.  Receive ys and a proof q that 0 < length ys, then
        -- listrec on ys.  The nil branch is unreachable but we return 0.
        | λ ys : list ℕ .
            λ q : {x : ℕ | 0 < length ys} .
              let {qv, pq} : {x : ℕ | 0 < length ys} = q in
              listrec [(zs : list ℕ) ↦ ℕ] ys
                | 0
                | hd, tl, _ih ↦ hd
        -- STEP: n = succ j.  IH `_rec : (ys : list ℕ) → {x | j < length ys} → ℕ`.
        -- Inner listrec on ys uses a *dependent* motive so the cons branch
        -- knows length zs = length tl + 1, enabling the proof discharge.
        | ‖succ j‖, _rec ↦
            λ ys : list ℕ .
            λ q : {x : ℕ | j + 1 < length ys} .
              (((listrec
                  [(zs : list ℕ) ↦ (q' : {x : ℕ | j + 1 < length zs}) → ℕ]
                  ys
                  -- nil branch: take q', destructure, ignore (unreachable).
                  | λ q' : {x : ℕ | j + 1 < length ([] : List Nat)} .
                      let {qv', pq'} : {x : ℕ | j + 1 < length ([] : List Nat)} = q' in 0
                  -- cons branch: peel hd, call _rec on tl.  From
                  -- q' : j + 1 < length (hd :: tl) = length tl + 1 we get
                  -- j < length tl.
                  | hd, tl, _ih ↦
                      λ q' : {x : ℕ | j + 1 < length (hd :: tl)} .
                        let {qv', pq'} : {x : ℕ | j + 1 < length (hd :: tl)} = q' in
                        (((_rec : (ys : list ℕ) → (q : {x : ℕ | j < length ys}) → ℕ) tl
                            : (q : {x : ℕ | j < length tl}) → ℕ)
                          ({0, by
                              have h : length (hd :: tl) = length tl + 1 := rfl
                              omega : j < length tl}
                            : {x : ℕ | j < length tl}))
                ) : (q' : {x : ℕ | j + 1 < length ys}) → ℕ) q)
      ) : (ys : list ℕ) → (q : {x : ℕ | idx < length ys}) → ℕ) xs
        : (q : {x : ℕ | idx < length xs}) → ℕ)
      ({0, p : idx < length xs} : {x : ℕ | idx < length xs})

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
      by
        rw [plus_eq, mult_eq, mult_eq]
        -- The let_set destructure projects rv := rows.val, cv := cols.val.
        -- These are the same expression; bridge so omega sees it.
        have hrv : rv = rows.val := rfl
        have hcv : cv = cols.val := rfl
        have h1 : iv + 1 ≤ rv := by rw [hrv]; omega
        have h2 : (iv + 1) * cv ≤ rv * cv := Nat.mul_le_mul_right cv h1
        have h3 : (iv + 1) * cv = iv * cv + cv := Nat.succ_mul iv cv
        rw [hcv] at h2 h3 ⊢; omega
      : plus (mult iv cv) jv < mult rv cv}
      : {k : ℕ | k < mult rows cols}

-- Same as `flatIndex`, but the nat-arithmetic obligation is discharged using
-- the `decidable_reduce` tactic.  After bridging `plus`/`mult` to `+`/`*` we
-- bundle the arithmetic into a conjunction: `jv < cv ∧ iv * cv + cv ≤ rv * cv`.
-- `decidable_reduce` splits it, closes the linear conjunct `jv < cv` via
-- `grind` (from `pj`), and hands back exactly the nonlinear conjunct
-- `iv * cv + cv ≤ rv * cv` as a subgoal for the user to discharge.
def flatIndex_decidable_reduce : (rows : {r : ℕ | r > 0})
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
      by
        rw [plus_eq, mult_eq, mult_eq]
        suffices both : jv < cv ∧ iv * cv + cv ≤ rv * cv by grind
        -- decidable_reduce closes `jv < cv` and leaves the nonlinear conjunct.
        decidable_reduce
        calc iv * cv + cv
            = (iv + 1) * cv := (Nat.succ_mul iv cv).symm
          _ ≤ rv * cv       :=
              Nat.mul_le_mul_right cv (by show iv + 1 ≤ rows.val; omega)
      : plus (mult iv cv) jv < mult rv cv}
      : {k : ℕ | k < mult rows cols}

-- `flatIndex` produces a value with refinement `< mult rows cols`.
-- `arr` carries refinement `length arr = mult rows cols`.  Together these say
-- `flatIndex rows cols i j < length arr` — exactly `get`'s precondition.
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
