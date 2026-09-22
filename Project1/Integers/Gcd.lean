import Project1.Integers.Arithmetic
import Project1.Nat.Properties
import Project1.Integers.Inequalities

import Std

namespace MyInt
open Classical

def IsGcd (a b d : Int) : Prop :=
  Int.Divides d a ∧
  Int.Divides d b ∧
  (∀ (c : Int), (Int.Divides c a) → (Int.Divides c b) → (Int.Divides c d)) ∧
  (d ≥ .zero)

theorem exists_gcd (a b : Int) :
  ∃ (d : Int), IsGcd a b d :=
    sorry

noncomputable
def Int.gcd (a b : Int) : Int :=
  by
    have h1 := exists_gcd a b
    exact Exists.choose h1

theorem gcd_is_gcd (a b : Int) :
  IsGcd a b (Int.gcd a b) := by
    unfold Int.gcd
    exact Exists.choose_spec (exists_gcd a b)

theorem one_is_unit (a : Int) (h1: a.Divides .one) : a = .one :=
  by sorry

theorem int_two_neq_one : Int.two ≠ Int.one :=
  by
    simp [(· ≠ · )]
    unfold Int.two
    unfold Int.one
    intro h
    have h2 := Quotient.exact h
    simp [(· ≈ · )] at h2
    unfold instHasEquivOfSetoid at h2
    unfold Setoid.r at h2
    simp at h2
    unfold intRepSetoid at h2
    simp at h2
    unfold IntRep.Equivalent at h2
    simp at h2
    rw[MyNat.add_zero] at h2
    rw[MyNat.add_zero] at h2
    rw[MyNat.Nat.two] at h2
    have h3 := MyNat.succ_is_different MyNat.Nat.one
    have h4 := And.intro h2 h3.symm
    have bad : False := h3.symm h2
    exact bad

theorem even_or_odd (a : Int) : (Int.Even a ∨ Int.Odd a) :=
  by
    sorry

theorem not_even_means_odd (a : Int ) (h1 : ¬ Int.Even a) : Int.Odd a :=
  by
    have h2 := even_or_odd a
    have h3 := Or.elim h2 h1
    simp at h3
    exact h3

theorem even_means_not_odd (a : Int) : (Int.Even a) →  (¬ Int.Odd a ) :=
  by
    sorry

theorem even_square_means_even (a : Int) (h1 : Int.Even (a*a)) : (Int.Even a) :=
  by
    apply Classical.byContradiction
    intro h0
    have h2 := not_even_means_odd a h0
    have h3 := odd_squared_is_odd a h2
    have h4 := even_means_not_odd (a * a) h1
    contradiction

theorem even_is_mult_of_two (a : Int) (h1 : Int.Even a) : (∃ (k : Int), a = .two * k) :=
  by
    unfold Int.Even at h1
    unfold Int.Divides at h1
    exact h1

theorem common_div_divides_gcd ( a b d : Int )
  (h1:  d.Divides a)
  (h2 : d.Divides b) :
  (d.Divides (Int.gcd a b)) :=
  by
    have hg := gcd_is_gcd a b
    unfold IsGcd at hg
    have h3 := hg.right.right.left d h1 h2
    exact h3

theorem even_means_two_divides (a : Int ) (h1 : Int.Even a) : Int.two.Divides a :=
  by
    unfold Int.Even at h1
    exact h1

theorem intofnat_eq (a b : Nat) (h1 : intOfNat a = intOfNat b) :
  (a = b) :=
  by
    induction a generalizing b with
    | zero =>
        dsimp [intOfNat] at h1
        have h2 := intofrep_eq (IntRep.mk .zero .zero) (IntRep.mk b .zero) h1
        simp at h2
        rw[MyNat.zero_add] at h2
        rw[MyNat.zero_add] at h2
        exact h2
    | succ a ih =>
        dsimp [intOfNat] at h1
        have h2 := intofrep_eq (IntRep.mk a.succ .zero) (IntRep.mk b .zero) h1
        simp at h2
        rw[MyNat.zero_add] at h2
        rw[MyNat.add_zero] at h2
        exact h2

theorem two_neq_zero : (Int.two ≠ .zero) :=
  by
    intro h1
    dsimp [Int.two, Int.zero] at h1
    have h2 := intofnat_eq MyNat.Nat.two MyNat.Nat.zero h1
    contradiction

theorem root2_irrational_1 :
  (¬ ∃ (a b : Int), (Int.gcd a b = Int.one) ∧ .two * b * b = a * a) :=
  by
    intro h
    obtain ⟨ a, ha ⟩ := h
    obtain ⟨ b, hb ⟩ := ha
    have h1 := hb.left
    have h2 := hb.right

    have h3 : (Int.two.Divides (a * a)) := by
      unfold Int.Divides
      exists (b * b)
      rw[<-int_mul_associates]
      exact h2.symm

    have h4 : (Int.Even (a * a)) := by
      unfold Int.Even
      exact h3

    have h5 : (Int.Even a) := even_square_means_even a h4

    have h6 : (∃ (k : Int), a = .two * k) := even_is_mult_of_two a h5

    obtain ⟨ k, hk ⟩ := h6

    rw[hk] at h2
    rw[int_mul_associates] at h2
    rw[int_mul_associates] at h2

    have h7 := mul_left_divides (b * b) (k * (.two * k)) .two h2
    rw[<-int_mul_associates] at h7
    rw[int_mul_commutes] at h7
    rw[int_mul_associates] at h7
    rw (occs := .pos [2]) [int_mul_commutes] at h7
    rw[int_mul_associates] at h7

    have h8 : (Int.Even (b * b)) := by
      unfold Int.Even
      exists (k * k)
      have h9 := h7 two_neq_zero
      rw[h9]

    have hbeven := even_square_means_even b h8

    have twoa : (Int.two.Divides a) := even_means_two_divides a h5
    have twob : (Int.two.Divides b) := even_means_two_divides b hbeven

    have h9 : (Int.two.Divides (Int.gcd a b )) := common_div_divides_gcd a b .two twoa twob

    rw[h1] at h9
    have h10 : (Int.two = Int.one) := one_is_unit .two h9
    have h12 := And.intro h10 int_two_neq_one
    simp at h12
end MyInt
