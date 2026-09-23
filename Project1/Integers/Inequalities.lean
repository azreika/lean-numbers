import Project1.Integers.Arithmetic
import Project1.IntReps.Inequalities
import Project1.Nat.Properties

import Std

namespace MyInt

def Int.lte : Int -> Int -> Prop :=
  Quotient.lift₂
    IntRep.lte
    (by
      intro a1 b1 a2 b2
      intro h1 h2

      have h3 : (a1.lte b1 = a1.lte b2) := lte_respects_right a1 b1 b2 h2
      have h4 : (a1.lte b2 = a2.lte b2) := lte_respects_left a1 a2 b2 h1
      have h5 : (a1.lte b1 = a2.lte b2) := Eq.trans h3 h4
      exact h5
    )

instance : LE IntRep where
  le := IntRep.lte
instance : LE Int where
  le := Int.lte

def Int.lt (a b : Int) : Prop :=
  a ≤ b ∧ a ≠ b

instance : LT Int where
  lt := Int.lt

theorem lte_trans ( a b c : Int) (h1 : a ≤ b ) (h2 : b ≤ c) :
  (a ≤ c) := sorry

theorem prod_geq_means_op_geq (a b : Int) (h1 : .zero ≤ a * b) (h2 : .zero ≤ a) :
  (.zero ≤ b) := sorry

theorem zero_leq_one : (Int.zero ≤ Int.one) := sorry
theorem zero_leq_two : (Int.zero ≤ Int.two) := sorry

theorem eq_means_leq ( a b : Int ) (h1 : a = b) :
  (a ≤ b ) := sorry

theorem geq_zero_means_prod_geq ( a b : Int ) ( h1 : .zero ≤ a ) (h2 : .zero ≤ b) :
  (a ≤ a * b) := sorry

theorem lte_antisym ( a b : Int ) (h1 : Int.lte a b ) (h2 : Int.lte b a) :
  (a = b) := by
  sorry

theorem zero_lt_means_one_lte ( a : Int ) (h1: .zero < a) :
  (.one ≤ a) := sorry

theorem geq_one_means_minus_geq_zero (a : Int) (h1 : .one ≤ a) :
  (.zero ≤ (a - .one)) :=
    sorry

theorem prod_nonzero_means_op_nonzero (a b : Int) (h1 : a * b ≠ .zero) :
  (a ≠ .zero) := sorry

theorem zero_lt_means_neq_zero (a : Int) (h1 : .zero < a) :
  (a ≠ .zero) := sorry

theorem lte_less_sum (a b : Int) (h1 : b ≥ .zero) :
  a ≤ a + b := sorry

theorem lt_means_lte (a b : Int) (h1 : a < b ) : (a ≤ b ) := sorry

theorem not_lt_means_flip_lte ( a b : Int) (h1 : ¬ (a < b)) :
  (b ≤ a) := sorry

theorem not_lte_means_flip_lt ( a b : Int) (h1 : ¬ (a ≤ b)) :
  (b < a) := sorry

theorem integer_gaps (a b : Int) (h1 : a ≤ b) :
  ∃ (m : Int), (.zero ≤ m) ∧ (b = a + m) := sorry

theorem negate_lte ( a b : Int ) (h1 : a ≤ b) :
  a.negate ≥ b.negate := sorry


theorem lt_means_neq ( a b : Int ) (h1: a < b) : a ≠ b := sorry

theorem sum_lte_is_lte (a b c : Int) (h1: a ≥ c) (h2: b ≥ c) :
  (a + b ≥ c) := sorry

theorem lt_plus_pos_means_lt (a b c: Int) (h1: a ≥ c) (h2 : b > .zero) :
  a + b > c := sorry

theorem lte_add_right (a b c : Int) ( h1 : a ≥ b ) : a + c ≥ b + c :=
  by
    sorry

theorem negative_zero_lte_from_lt ( a : Int) (h1 : a < .zero) :
  (a.negate > .zero) :=
  by
    sorry

theorem int_succ_one (a : Nat) :
  intOfNat (a.succ) = (intOfNat a) + .one :=
  by
    dsimp [Int.one]
    dsimp [intOfNat]
    dsimp [intOfRep]
    apply Quotient.sound
    apply unfold_intrep_equiv_congr
    dsimp [IntRep.Equivalent]
    dsimp [IntRep.add]
    rw[MyNat.add_zero]
    rw[MyNat.add_zero]
    rw[MyNat.add_zero]
    rw[MyNat.add_one]
    rw[MyNat.add_commutes]

theorem int_nat_succ (a : Nat) (b : Int) (h1 : b = intOfNat a) :
  (b + .one = intOfNat (a.succ)) :=
  by
    induction a generalizing b with
    | zero =>
    rw[<-Int.zero] at h1
    rw[h1]
    rw[int_zero_add]
    rfl
    | succ a ih =>
    rw[int_succ_one]
    rw[int_succ_one]
    apply add_right_congr
    apply add_right_cancel (c := Int.one.negate)
    rw[int_add_associates]
    rw[inverse_nat]
    rw[int_add_zero]
    rw[int_succ_one] at h1
    have h2 := add_right_congr b (intOfNat a + Int.one) Int.one.negate h1
    rw[h2]
    rw[int_add_associates]
    rw[inverse_nat]
    rw[int_add_zero]

theorem intrep_apos ( a b c d : Nat) (h1 : (IntRep.mk a b) ≤ (IntRep.mk c d) ) :
  MyNat.Nat.lte (a + d) (c + b) := by exact h1

theorem intofrep_apos (a b c d : Nat ) (h1 : intOfRep (IntRep.mk a b) ≤ intOfRep (IntRep.mk c d)) :
  MyNat.Nat.lte (a  +d ) (c + b) := by exact h1

theorem nonneg_is_nat (a : Int):
  (a ≥ .zero) → (∃ (k : Nat), (a = intOfNat k) ):=
  by
    dsimp [intOfNat]
    refine Quotient.inductionOn a ?_
    intro x
    dsimp [intOfRep]
    intro h1
    cases x with
    | mk apos aneg  =>
    have hpos : (MyNat.Nat.lte aneg apos) := by
      simp only [( · ≥ · )] at h1
      simp only [( · ≤  · )] at h1
      rw[<-intOfRep] at h1
      rw[Int.zero] at h1
      rw[intof_nat_to_rep] at h1
      have hx := intofrep_apos .zero .zero apos aneg h1
      rw[MyNat.zero_add] at hx
      rw[MyNat.add_zero] at hx
      exact hx
    have h2 := MyNat.natural_gap aneg apos hpos
    obtain ⟨ m, hm ⟩ := h2
    exists m
    apply Quotient.sound
    apply unfold_intrep_equiv_congr
    dsimp[IntRep.Equivalent]
    rw[MyNat.add_zero]
    have hm2 := hm.symm
    rw[add_commutes] at hm2
    exact hm2

end MyInt
