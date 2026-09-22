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

end MyInt
