def hello := "world"
-- #eval "Hello"
-- #check 2+2
def f (x : Nat) := x + 3
-- #check f

theorem easy : 2 + 2 = 4
  := rfl

#check easy
def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem hard : FermatLastTheorem
  := sorry

#check hard

-- import
-- example (a b c : ℝ): (a * b) * c = b * (a * c) := by
--   rw [mul]
