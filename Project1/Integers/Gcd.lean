import Project1.Integers.Arithmetic
import Project1.Nat.Properties
import Project1.Integers.Inequalities
import Project1.Integers.Sets

import Std

namespace MyInt
open Classical

def IsGcd (a b d : Int) : Prop :=
  Int.Divides d a ∧
  Int.Divides d b ∧
  (∀ (c : Int), (Int.Divides c a) → (Int.Divides c b) → (Int.Divides c d)) ∧
  (d ≥ .zero)

theorem euclidean ( a b : Int ) (ha : .zero ≤ a) (hb : .zero < b):
  ∃ (r q : Int),
    (r = q * b - a) ∧
    (.zero ≤ r) ∧
    (r < b) :=
  by
    let A : Set Int := fun x => ∃ q : Int, (x = b * q - a) ∧ (.zero ≤ x)

    have b_geq_one := zero_lt_means_one_lte b hb
    have b_minus_one_geq_zero := geq_one_means_minus_geq_zero b b_geq_one

    have A_nonempty : (is_nonempty A ) := by
      unfold is_nonempty
      exists (a * b - a)
      simp only [(· ∈ ·)]
      unfold A
      exists a
      constructor
      rw[int_mul_commutes]
      rw[sub_is_plus_neg]
      rw[negate_to_mul_neg_one]
      rw[<-mul_add_distributes]
      rw[<-sub_is_plus_neg]
      have hh := geq_zero_means_prod_geq a (b-Int.one) ha b_minus_one_geq_zero
      have hh2 := lte_trans Int.zero a (a * (b-Int.one)) ha hh
      exact hh2
    have A_all_pos : (∀ (x : Int), x ∈ A → x ≥ .zero) := by
      intro x
      intro x_in_A
      simp only [(· ∈ ·)] at x_in_A
      unfold A at x_in_A
      obtain ⟨ _, hh ⟩ := x_in_A
      exact hh.right
    have A_hasmin : (has_min A) := pos_nonempty_has_min A A_nonempty A_all_pos
    unfold has_min at A_hasmin
    obtain ⟨ r, hr ⟩ := A_hasmin
    exists r
    have b_geq_zero : (b ≥ .zero) := lt_means_lte .zero b hb
    have r_in_A : (r ∈ A) := by
      unfold is_min at hr
      exact hr.left
    simp only [(· ∈ ·)] at r_in_A
    unfold A at r_in_A
    obtain ⟨ q, hq ⟩ := r_in_A
    have r_geq_zero := hq.right
    have hq := hq.left
    rw[int_mul_commutes] at hq

    exists q
    constructor

    exact hq

    constructor
    exact r_geq_zero

    apply Classical.byContradiction
    intro h

    have hbb : (b ≤ r) := not_lt_means_flip_lte r b h
    have gap_exists : ∃ (m : Int), (.zero ≤ m) ∧ (r = b + m) := integer_gaps b r hbb
    obtain ⟨ m, hm ⟩ := gap_exists
    have hm1 := hm.left
    have hm2 := hm.right
    rw[hm2] at hq
    have hq2 : (m = q * b - a - b) := by
      have hh : (b.negate + (b + m)) = (b.negate + (q * b -a)) :=
        add_left_congr (b+m) (q*b-a) b.negate hq
      rw[<-int_add_associates] at hh
      rw (occs := .pos [2]) [int_add_commutes] at hh
      rw[inverse_nat] at hh
      rw[int_zero_add] at hh
      rw[int_add_commutes] at hh
      rw[<-sub_is_plus_neg] at hh
      exact hh
    have hq3 : (m = (q - .one) * b - a) := by
      rw[int_mul_commutes]
      rw[sub_is_plus_neg]
      rw[sub_is_plus_neg]
      rw[mul_add_distributes]
      rw[int_mul_commutes]
      rw[int_expand_negate]
      rw[int_mul_one]
      rw [int_add_associates]
      rw (occs := .pos [2]) [int_add_commutes]
      rw[<-int_add_associates]
      rw[<-sub_is_plus_neg]
      rw[<-sub_is_plus_neg]
      exact hq2
    have m_in_A : (m ∈ A) := by
      simp only [(· ∈ · )]
      unfold A
      exists (q - Int.one)
      rw[int_mul_commutes]
      constructor
      exact hq3
      exact hm1
    have r_less_than_m : (r ≤ m) := by
      unfold is_min at hr
      exact hr.right m m_in_A
    have m_less_than_r : (m ≤ r) := by
      have hh := lte_less_sum m b b_geq_zero
      rw[int_add_commutes] at hh
      rw[<-hm2] at hh
      exact hh
    have m_eq_r : m = r := lte_antisym m r m_less_than_r r_less_than_m
    have b_eq_zero : b = .zero := by
      rw[m_eq_r] at hm2
      have h11 := add_left_congr r (b + r) .zero hm2
      rw (occs := .pos [2]) [int_zero_add] at h11
      have hh := add_left_cancel Int.zero b r h11
      exact hh.symm
    have b_neq_zero : b ≠ .zero := zero_lt_means_neq_zero b hb
    contradiction

theorem exists_gcd_pos ( a b : Int) (ha: a ≥ .zero) (hb : b ≥ .zero) :
  ∃ (d : Int), IsGcd a b d :=
  by
    let pos_com_set : Set Int := PosLinearCombinations a b
    have h_has_element : (is_nonempty pos_com_set) := sorry
    have h_has_min : (has_min pos_com_set) := sorry
    unfold has_min at h_has_min
    obtain ⟨ d, hd ⟩ := h_has_min
    exists (d)
    unfold IsGcd
    have d_in_poscom : (d ∈ pos_com_set) := sorry
    have d_gt_zero : (.zero < d) := sorry

    have d_divides_a : (d.Divides a ) := by
      have hh := euclidean a d ha d_gt_zero
      obtain ⟨ r, hr ⟩ := hh
      obtain ⟨ q, hq ⟩ := hr
      have hq1 := hq.left
      have hq2 := hq.right.left
      have hq3 := hq.right.right

      have r_eq_zero : (r = .zero) := by sorry
      unfold Int.Divides
      exists q
      rw[r_eq_zero] at hq1
      have hh2 : (.zero + a) = (q * d - a) + a := sorry
      rw[int_zero_add] at hh2
      rw[sub_is_plus_neg] at hh2
      rw[int_add_associates] at hh2
      rw (occs := .pos [2]) [int_add_commutes] at hh2
      rw[inverse_nat] at hh2
      rw[int_add_zero] at hh2
      rw[int_mul_commutes] at hh2
      exact hh2

    have d_divides_b : (d.Divides b) := by
      have hh := euclidean b d hb d_gt_zero
      obtain ⟨ r, hr ⟩ := hh
      obtain ⟨ q, hq ⟩ := hr
      have hq1 := hq.left
      have hq2 := hq.right.left
      have hq3 := hq.right.right

      have r_eq_zero : (r = .zero) := by sorry
      unfold Int.Divides
      exists q
      rw[r_eq_zero] at hq1
      have hh2 : (.zero + b) = (q * d - b) + b := sorry
      rw[int_zero_add] at hh2
      rw[sub_is_plus_neg] at hh2
      rw[int_add_associates] at hh2
      rw (occs := .pos [2]) [int_add_commutes] at hh2
      rw[inverse_nat] at hh2
      rw[int_add_zero] at hh2
      rw[int_mul_commutes] at hh2
      exact hh2

    constructor
    exact d_divides_a

    constructor
    exact d_divides_b

    constructor

    intro c
    intro c_divides_a
    intro c_divides_b
    unfold Int.Divides at c_divides_a
    unfold Int.Divides at c_divides_b
    obtain ⟨ k_a, hk_a ⟩ := c_divides_a
    obtain ⟨ k_b, hk_b ⟩ := c_divides_b

    have c_gt_zero : (c > .zero) := sorry
    have hh := euclidean b c hb c_gt_zero
    obtain ⟨ r, hr ⟩ := hh
    obtain ⟨ q, hq ⟩ := hr
    have hq1 := hq.left
    have hq2 := hq.right.left
    have hq3 := hq.right.right

    have r_eq_zero : (r = .zero) := by sorry
    unfold Int.Divides
    exists q
    rw[r_eq_zero] at hq1
    have hh2 : (.zero + d) = (q * c - d) + d := sorry
    rw[int_zero_add] at hh2
    rw[sub_is_plus_neg] at hh2
    rw[int_add_associates] at hh2
    rw (occs := .pos [2]) [int_add_commutes] at hh2
    rw[inverse_nat] at hh2
    rw[int_add_zero] at hh2
    rw[int_mul_commutes] at hh2

    exact hh2

    exact lt_means_lte Int.zero d d_gt_zero

theorem exists_gcd (a b : Int):
  ∃ (d : Int), IsGcd a b d :=
  by
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

theorem one_is_unit (a : Int) (h1: a.Divides .one) (h2: .zero ≤ a) : a = .one :=
  by
    dsimp [Int.Divides] at h1
    obtain ⟨ k, hk ⟩ := h1
    have hh : (.one ≤ a * k) := by
      exact eq_means_leq .one (a*k) hk
    have hh' : (Int.zero ≤ .one ) := zero_leq_one
    have h3_0 : (.zero ≤ a * k) := by
      rw[hk] at hh'
      exact hh'
    have h3 : (.zero ≤ k) := prod_geq_means_op_geq a k h3_0 h2
    have h4 : (a ≤ a * k) := geq_zero_means_prod_geq a k h2 h3
    have h4_1 : (a * k ≠ .zero) := by
      intro bb
      rw[bb] at hk
      have h4_2 : MyNat.Nat.one = MyNat.Nat.zero := intofnat_eq MyNat.Nat.one MyNat.Nat.zero hk
      contradiction
    have h5 : (a ≤ .one) := by
      rw[hk]
      exact h4
    have h6 : (a ≠ .zero) := prod_nonzero_means_op_nonzero a k h4_1
    have h7 : (.one ≤ a) := by
      have hlt : (Int.zero < a ) := by
        have hh := And.intro h2 h6
        simp only [(· < · )]
        unfold Int.lt
        constructor
        exact hh.left
        exact hh.right.symm
      have hh := zero_lt_means_one_lte a hlt
      exact hh
    have h8 : (a = .one ) := lte_antisym a .one h5 h7
    exact h8

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
    have h10 : (Int.two = Int.one) := one_is_unit .two h9 zero_leq_two
    have h12 := And.intro h10 int_two_neq_one
    simp at h12

end MyInt
