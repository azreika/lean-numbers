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

theorem lte_trans ( a b c : Int) (h1 : a ≤ b ) (h2 : b ≤ c) :
  (a ≤ c) := sorry

theorem prod_geq_means_op_geq (a b : Int) (h1 : .zero ≤ a * b) (h2 : .zero ≤ a) :
  (.zero ≤ b) := sorry

theorem zero_leq_one : (Int.zero ≤ Int.one) := sorry

theorem eq_means_leq ( a b : Int ) (h1 : a = b) :
  (a ≤ b ) := sorry

theorem geq_zero_means_prod_geq ( a b : Int ) ( h1 : .zero ≤ a ) (h2 : .zero ≤ b) :
  (a ≤ a * b) := sorry

theorem lte_antisym ( a b : Int ) (h1 : Int.lte a b ) (h2 : Int.lte b a) :
  (a = b) := by
  sorry

theorem zero_lt_means_one_lte ( a : Int ) (h1: .zero ≤ a ) (h2 : a ≠ .zero) :
  (.one ≤ a) := sorry

theorem prod_nonzero_means_op_nonzero (a b : Int) (h1 : a * b ≠ .zero) :
  (a ≠ .zero) := sorry

end MyInt
