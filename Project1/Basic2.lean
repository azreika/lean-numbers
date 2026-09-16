-- rfl: X = X
import mathlib

def Eq1 : Prop
  := ∀ (x q: Nat), 37 * x + q = 37 * x + q

theorem Eq1Proof : Eq1 := by
  intro x q
  rfl

example (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : Nat) (h : y = x + 7) : 2*y = 2 * (x+7) := by
  rw [h]
