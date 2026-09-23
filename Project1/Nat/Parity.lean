import Project1.Nat.Properties

namespace MyNat

theorem odd_or_even (n : Nat) :
  Nat.Odd n ∨ Nat.Even n := by
  induction n with
  | zero =>
    right
    unfold Nat.Even
    apply divides_zero
  | succ n ih =>
    cases ih with
    | inl hOdd =>
      right
      apply odd_succ_is_even
      apply hOdd
    | inr hEven =>
      left
      apply even_succ_is_odd
      apply hEven

end MyNat
