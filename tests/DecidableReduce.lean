import Ambifine.Tactics

example (x y : Nat) (hx : x = 1) (hy : y = 3) :
    x < 2 ∧ y + x < 5 ∧ y * x > 0 ∧ x * x + 3 ≥ 4 := decidable_reduce
  · subst hx; subst hy; decide
  · subst hx; decide

-- Purely linear goal: `decidable_reduce` closes it entirely with no leftover subgoals.
example (a b : Nat) (h1 : a < b) (h2 : b < 10) : a < 10 ∧ a + 1 ≤ b := decidable_reduce

-- Single nonlinear atom: `decidable_reduce` returns the goal unchanged to the user.
example (x : Nat) (hx : x ≥ 2) : x * x ≥ 4 := decidable_reduce
  exact Nat.mul_le_mul hx hx

-- Conjunction with one linear, one nonlinear conjunct.
example (n : Nat) (h : n ≥ 3) : n + 1 > 3 ∧ n * n ≥ 9 := decidable_reduce
  exact Nat.mul_le_mul h h
