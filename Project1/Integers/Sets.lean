
import Project1.Integers.Integers
import Project1.Integers.Arithmetic
import Project1.Integers.Inequalities

namespace MyInt

def Set (a : Type) := a -> Prop
instance { a : Type } : Membership a (Set a) where
  mem s x := s x

def LinearCombinations (a b : Int) : Set Int :=
  fun x => ∃ m n : Int, x = a * m + b * n

def PosLinearCombinations ( a b : Int ) : Set Int :=
  fun x => (x ∈ (LinearCombinations a b) ∧ .zero < x)

def is_min (x : Int) (s: Set Int) : Prop :=
  x ∈ s ∧ (
    ∀ (y : Int), (y ∈ s → x ≤ y)
  )

def has_min (s : Set Int) : Prop :=
  ∃ (m : Int), is_min m s

def is_nonempty (s : Set Int) : Prop :=
  ∃ (x : Int), x ∈ s

theorem pos_nonempty_has_min (s : Set Int) (h1: is_nonempty s) (h2 : ∀ (x : Int), (x ∈ s → .zero ≤ x)) :
  has_min s :=
    sorry

theorem expand_poscom_set ( x a b : Int ) :
  (x ∈ PosLinearCombinations a b) ↔ (∃ (m n : Int), x = a * m + b * n) ∧ .zero < x :=
  by
    constructor

    intro h1
    simp only [(· ∈ · )] at h1
    unfold PosLinearCombinations at h1
    unfold LinearCombinations at h1
    simp only [(· ∈ · )] at h1
    exact h1

    intro h1
    simp only [(· ∈ · )]
    unfold PosLinearCombinations
    unfold LinearCombinations
    simp only [(· ∈ · )]
    exact h1

end MyInt
