import Project1.Integers.Integers
import Project1.Nat.Properties

import Std

namespace MyInt

theorem int_add_zero (a : Int) :
  a + zero = a :=
  by
    refine Quotient.inductionOn a ?_
    intro x
    rw[<-intOfRep]
    unfold zero
    rw[<-add_mk]
    unfold zero_int_rep
    cases x with
    | mk pos neg =>
      dsimp[Int]
      apply Quotient.sound
      change (IntRep.mk pos neg ) + (IntRep.mk .zero .zero) ≈ (IntRep.mk pos neg)
      change (IntRep.mk (pos + .zero) (neg + .zero) ) ≈ (IntRep.mk pos neg)
      rw[MyNat.add_zero]
      rw[MyNat.add_zero]
      exact equi_refl (IntRep.mk pos neg)

theorem int_add_associates (a b c : Int ) :
  (a + b) + c = a + (b + c ) := sorry

theorem int_mul_associates (a b c : Int ) :
  (a * b) * c = a * (b * c ) := sorry


theorem int_mul_commutes ( a b : Int ) :
  a * b = b * a :=
    sorry

theorem int_add_commutes ( a b : Int ) :
  a + b = b + a :=
  by
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-add_mk]
    rw[<-add_mk]
    cases x with
    | mk xpos xneg =>
      dsimp[Int]
      apply Quotient.sound
      cases y with
      | mk ypos yneg =>
        change (IntRep.mk xpos xneg ) + (IntRep.mk ypos yneg) ≈
                (IntRep.mk ypos yneg ) + (IntRep.mk xpos xneg)
        change (IntRep.mk (xpos + ypos) (xneg + yneg)) ≈
                (IntRep.mk (ypos + xpos) (yneg+xneg) )
        rw[add_commutes]
        rw (occs := .pos [2]) [add_commutes]
        exact equi_refl (IntRep.mk (ypos + xpos) (yneg+xneg) )

theorem int_zero_add ( a : Int ) :
  zero + a = a :=
  by
    rw[int_add_commutes]
    rw[int_add_zero]

theorem add_left_cancel (a b c : Int ) (h1 : a = b) :
  (a + c = b + c) :=
  by sorry

theorem left_divides ( p m : Int ) :
  (p.Divides (p*m)) :=
  by
    unfold Int.Divides
    exists m

theorem int_expand_negate ( a b : Int ) :
  a * (b.negate) = (a * b).negate := sorry

theorem drop_negate ( a : Int ) (h1: a.negate = b.negate ) :
  a = b := sorry

theorem add_negate ( a : Int ) (h1: a = b) :
  a.negate = b.negate := sorry

theorem divides_neg ( p m : Int ) (h1 : p.Divides m ):
  (p.Divides m.negate) :=
  by
    unfold Int.Divides
    unfold Int.Divides at h1
    obtain ⟨ k, hk ⟩ := h1
    exists (k.negate)
    rw [int_expand_negate]
    apply add_negate
    exact hk

theorem divides_sum ( p a b : Int ) (h1: p.Divides a) (h2 : p.Divides b) :
  (p.Divides (a + b)) := sorry

theorem prime_divisible_sum
    ( p a b : Int )
    ( h2 : Int.Divides p a )
    ( h3 : Int.Divides p ( a + b )) :
  Int.Divides p b :=
  by
    unfold Int.Divides at h2
    obtain ⟨ k , hk ⟩ := h2

    unfold Int.Divides at h3
    obtain ⟨ m , hm ⟩ := h3

    rw[hk] at hm
    have h2 := add_left_cancel (p*k + b) (p*m) (p*k).negate hm
    rw[int_add_commutes] at h2
    rw[<-int_add_associates] at h2
    rw[int_add_commutes] at h2
    rw (occs := .pos [2]) [int_add_commutes] at h2
    rw[inverse_nat] at h2
    rw[int_add_zero] at h2

    have h3 : p.Divides (p * m) := left_divides p m
    have h4 : p.Divides (p * k) := left_divides p k
    have h5 : p.Divides (p * k).negate := divides_neg p (p*k) h4
    have h6 := divides_sum p (p*m) (p*k).negate h3 h5
    rw[<-h2] at h6
    exact h6


theorem even_squared_is_even (n : Int) (h1: Int.Even n) : (Int.Even (n * n)) :=
  by
    unfold Int.Even
    unfold Int.Even at h1
    unfold Int.Divides at h1
    obtain ⟨ k , hk ⟩ := h1
    rw[hk]
    rw[int_mul_associates]
    unfold Int.Divides
    exists (k * (two * k))


theorem mul_add_distributes ( a b c : Int ) :
  a * (b + c) = a * b + a * c :=
  by
    sorry

theorem add_left_congr ( a b c : Int ) ( h1 : a = b ) :
  (c + a = c + b) :=
  by
    sorry
theorem add_right_congr ( a b c : Int ) ( h1 : a = b ) :
(a + c = b + c) :=
  by
    sorry

theorem mul_left_congr ( a b c : Int ) ( h1 : a = b ) :
(c * a = c * b) :=
  by
    sorry

theorem mul_left_divides( a b c : Int ) ( h1 : c * a = c * b ) :
(a = b) :=
  by
    sorry

theorem rearrange_22k (k : Int ) :
  (two * (two * k)) = (four * k) := sorry

theorem rearrange_22k_2 ( k : Int ) :
  (two * k + two * k) = (four * k) := sorry

theorem int_mul_one ( a : Int ) : a * one = a := by sorry

theorem odd_squared_is_odd (n : Int) (h1 : Int.Odd n) : (Int.Odd (n * n)) :=
  by
    unfold Int.Odd
    unfold Int.Odd at h1
    obtain ⟨ k, hk ⟩ := h1
    rw[hk]
    exists (two*k*k + two * k)
    rw[mul_add_distributes]
    rw[mul_add_distributes]
    rw[int_mul_one]
    rw[int_add_commutes]
    rw (occs := .pos [2]) [int_add_commutes]
    rw (occs := .pos [4]) [int_add_commutes]
    rw [int_add_associates]
    apply add_left_congr
    rw (occs := .pos [2]) [int_mul_commutes]
    rw[mul_add_distributes]
    rw[int_mul_one]
    rw[rearrange_22k]
    rw (occs := .pos [2]) [int_mul_associates]
    rw[rearrange_22k]
    rw[int_add_commutes]
    rw[int_add_associates]
    rw[rearrange_22k_2]
    apply add_right_congr
    rw[int_mul_associates]
    rw (occs := .pos [2]) [int_mul_commutes]
    rw[int_mul_associates]
    rw[rearrange_22k]

def Int.gcd : Int -> Int ->  Int := by sorry

theorem one_is_unit (a : Int) (h1: a.Divides one) : a = one :=
  by sorry

theorem int_two_neq_one : two ≠ one :=
  by
    simp [(· ≠ · )]
    unfold two
    unfold one
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

theorem not_even_means_odd (a : Int ) (h1 : ¬ Int.Even a) : Int.Odd a :=
  by
    sorry

theorem even_means_not_odd (a : Int) (h1 : Int.Even a) : (¬ Int.Odd a ) := sorry

theorem even_square_means_even (a : Int) (h1 : Int.Even (a*a)) : (Int.Even a) :=
  by
    apply Classical.byContradiction
    intro h0
    have h2 := not_even_means_odd a h0
    have h3 := odd_squared_is_odd a h2
    have h4 := even_means_not_odd (a * a) h1
    contradiction

theorem even_is_mult_of_two (a : Int) (h1 : Int.Even a) : (∃ (k : Int), a = two * k) :=
  by
    unfold Int.Even at h1
    unfold Int.Divides at h1
    exact h1

theorem common_div_divides_gcd ( a b d : Int )
  (h1:  d.Divides a)
  (h2 : d.Divides b) :
  (d.Divides (Int.gcd a b)) := sorry

theorem even_means_two_divides (a : Int ) (h1 : Int.Even a) : two.Divides a :=
  by
    unfold Int.Even at h1
    exact h1

theorem root2_irrational_1 :
  (¬ ∃ (a b : Int), (Int.gcd a b = one) ∧ two * b * b = a * a) :=
  by
    intro h
    obtain ⟨ a, ha ⟩ := h
    obtain ⟨ b, hb ⟩ := ha
    have h1 := hb.left
    have h2 := hb.right

    have h3 : (two.Divides (a * a)) := by
      unfold Int.Divides
      exists (b * b)
      rw[<-int_mul_associates]
      exact h2.symm

    have h4 : (Int.Even (a * a)) := by
      unfold Int.Even
      exact h3

    have h5 : (Int.Even a) := even_square_means_even a h4

    have h6 : (∃ (k : Int), a = two * k) := even_is_mult_of_two a h5

    obtain ⟨ k, hk ⟩ := h6

    rw[hk] at h2
    rw[int_mul_associates] at h2
    rw[int_mul_associates] at h2

    have h7 := mul_left_divides (b * b) (k * (two * k)) two h2
    rw[<-int_mul_associates] at h7
    rw[int_mul_commutes] at h7
    rw[int_mul_associates] at h7
    rw (occs := .pos [2]) [int_mul_commutes] at h7
    rw[int_mul_associates] at h7

    have h8 : (Int.Even (b * b)) := by
      unfold Int.Even
      exists (k * k)

    have hbeven := even_square_means_even b h8

    have twoa : (two.Divides a) := even_means_two_divides a h5
    have twob : (two.Divides b) := even_means_two_divides b hbeven

    have h9 : (two.Divides (Int.gcd a b )) := common_div_divides_gcd a b two twoa twob

    rw[h1] at h9
    have h10 : (two = one) := one_is_unit two h9
    have h12 := And.intro h10 int_two_neq_one
    simp at h12

end MyInt
