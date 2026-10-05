import Project1.Integers.Inequalities
import Project1.Integers.Arithmetic
import Project1.Nat.Parity
import Project1.Integers.Gcd

namespace MyInt

def Int.Unit (a : Int) : Prop :=
  a.Divides .one

def Int.coprime (a b : Int) : Prop :=
  Int.gcd a b = .one

theorem one_is_unit_prop : Int.Unit .one :=
  by
    dsimp [Int.Unit]
    dsimp [Int.Divides]
    exists Int.one

theorem self_dividing (a : Int) : a.Divides a := by
  dsimp [Int.Divides]
  exists Int.one
  simp

theorem all_div_one_means_unit (a : Int) (h1: ∀ (p : Int), p.Divides a → Int.Unit p) :
  a.Unit := by
    have h2 := h1 a (self_dividing a)
    exact h2

theorem mul_left_one (a b : Int) (h1 : a = a * b) : b = .one := by
  sorry

theorem mul_left_one_rev (a b : Int) (h1 : b = .one) : (a = a * b) := by
  sorry

theorem pos_divs_of_one (a : Int) (h1 : a ≥ .zero) (h2 : a.Divides .one) :
  a = .one := by
    sorry

theorem divs_of_one (a : Int) (h1 : a.Divides Int.one) : a = .one ∨ a = Int.one.negate :=
  by
    by_cases a_sign : a ≥ .zero
    left
    exact pos_divs_of_one a a_sign h1

    right
    have a_lte_zero := lt_means_lte a Int.zero (not_lte_means_flip_lt Int.zero a a_sign)
    have a_neg_sign := negate_lte a Int.zero a_lte_zero
    simp at a_neg_sign



    sorry

theorem prod_means_div_left (a b c : Int) (h1 : a * b = c) : a.Divides c :=
  by
    dsimp [Int.Divides]
    exists b
    exact h1.symm

theorem prod_means_div_right (a b c : Int) (h1 : a * b = c) : b.Divides c :=
  by
    rw[int_mul_commutes] at h1
    exact prod_means_div_left b a c h1

theorem unit_means_one_or_negone ( a : Int ) (h1 : a.Unit) : (a = .one ∨ a = Int.one.negate) :=
  by
    dsimp [Int.Unit, Int.Divides] at h1
    obtain ⟨ k, hk ⟩ := h1
    have a_divides_one := prod_means_div_left a k Int.one hk.symm
    exact divs_of_one a a_divides_one

theorem gcd_gt_zero (a b d : Int) (h1 : d = Int.gcd a b) : d > .zero :=
  by
    dsimp [Int.gcd] at h1
    sorry

theorem neg_one_lt_zero : Int.one.negate < .zero := by
  sorry

theorem divs_of_gcd_div_ab (a b d c : Int) (h1 : d = Int.gcd a b) (h2 : c.Divides d) :
  (c.Divides a ∧ c.Divides b) := by sorry

theorem lt_both_impossible (a b : Int) (h1: a < b) (h2 : b < a) : False :=
  by
    sorry

theorem prod_of_coprime (d a b : Int) (h1 : d.Divides (a * b)) (h2 : (Int.coprime d b)) :
  d.Divides a := by
  sorry

theorem gcd_is_min_poslin ( a b d : Int) (h1 : d = Int.gcd a b) :
  is_min d (PosLinearCombinations a b) := by sorry

theorem pos_divisors_of_two ( d : Int ) (h1 : d > .zero) (h2 : d.Divides .two) :
  d = .one ∨ d = .two :=
  by
    sorry

theorem chap1_q10 (u v : Int) (h1 : Int.gcd u v = .one) :
  (Int.gcd (u + v) (u -v)) = .one ∨
  (Int.gcd (u + v) (u-v)) = .two :=
  by
    let d := Int.gcd (u + v) (u -v )
    have hd : d = Int.gcd (u + v) (u -v ) := rfl
    rw[<-hd]

    have h2 := gcd_is_min_poslin (u + v) (u - v) d hd
    dsimp [is_min] at h2
    have h3 := h2.left
    have h4 := h2.right

    have h5 : (.two * u) ∈ PosLinearCombinations (u + v) (u - v) := sorry
    have h6 : (.two * v) ∈ PosLinearCombinations (u + v) (u - v) := sorry

    have h7 : (d.Divides (.two * u)) := sorry
    have h8 : (d.Divides (.two * v)) := sorry

    by_cases div_u : d.Divides u
    by_cases div_v : d.Divides v

    have h9 : d.Divides (Int.gcd u v) := sorry
    have h10: d.Divides .one := sorry
    have h11 : d ≥ .zero := sorry
    have h12 : d = Int.one := sorry
    left
    exact h12

    have h10 : d.Divides Int.two := sorry
    have h11 : d ≥ .zero := sorry

    have h12 : d = .one ∨ d = .two := sorry
    exact h12

    have coprime_u : d.coprime u := sorry
    have h9 : d.Divides Int.two := prod_of_coprime d Int.two u h7 coprime_u
    have h11 : d > .zero := gcd_gt_zero (u+v) (u-v) d hd

    have h12 : d = .one ∨ d = .two := pos_divisors_of_two d h11 h9
    exact h12

end MyInt
