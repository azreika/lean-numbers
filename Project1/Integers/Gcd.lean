import Project1.Integers.Arithmetic
import Project1.Nat.Properties
import Project1.Integers.Inequalities
import Project1.Integers.Sets
import Project1.Integers.Parity

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
      have hh := add_right_cancel Int.zero b r h11
      exact hh.symm
    have b_neq_zero : b ≠ .zero := zero_lt_means_neq_zero b hb
    contradiction

theorem gt_zero_plus_gte_zero (a b : Int) (h1: a > .zero) (h2 : b ≥ .zero) :
  (a + b  > .zero) :=
  by
    simp only [(· > · )]
    simp only [(· < · )]
    unfold Int.lt
    constructor

    have hh := lt_means_lte Int.zero a h1
    exact sum_lte_is_lte a b Int.zero hh h2

    have hh := lt_plus_pos_means_lt b a Int.zero  h2 h1
    rw[int_add_commutes] at hh
    exact lt_means_neq Int.zero (a + b) hh

theorem exists_gcd_pos ( a b : Int) (ha: a ≥ .zero) (hbz : b > .zero) :
  ∃ (d : Int), IsGcd a b d :=
  by
    have hb : (b ≥ .zero) := lt_means_lte .zero b hbz
    let pos_com_set : Set Int := PosLinearCombinations a b
    have h_has_element : (is_nonempty pos_com_set) := by
      unfold is_nonempty
      exists (a + b)
      simp only [(· ∈ · )]
      unfold pos_com_set
      unfold PosLinearCombinations
      unfold LinearCombinations
      constructor
      simp only [(· ∈ · )]
      exists Int.one
      exists Int.one
      rw[int_mul_one]
      rw[int_mul_one]
      have hx : (b + a > .zero) := gt_zero_plus_gte_zero b a hbz ha
      rw[int_add_commutes] at hx
      exact hx
    have all_pos : (∀ (x : Int), x ∈ pos_com_set → x ≥ .zero) := by
      intro x
      simp only [(· ∈ · )]
      unfold pos_com_set
      unfold PosLinearCombinations
      intro hh
      have hh2 := hh.right
      exact lt_means_lte Int.zero x hh2
    have h_has_min : (has_min pos_com_set) :=
      pos_nonempty_has_min pos_com_set h_has_element all_pos
    unfold has_min at h_has_min
    obtain ⟨ d, hd ⟩ := h_has_min
    exists (d)
    unfold IsGcd
    have d_in_poscom : (d ∈ pos_com_set) := by
      unfold is_min at hd
      exact hd.left
    have d_gt_zero : (.zero < d) := by
      simp only [(· ∈ · )] at d_in_poscom
      unfold pos_com_set at d_in_poscom
      unfold PosLinearCombinations at d_in_poscom
      exact d_in_poscom.right

    have d_divides_a : (d.Divides a) := by
      have hh := euclidean a d ha d_gt_zero
      obtain ⟨ r, hr ⟩ := hh
      obtain ⟨ q, hq ⟩ := hr
      have hq1 := hq.left
      have hq2 := hq.right.left
      have hq3 := hq.right.right

      have ham_d : (∃ (m n : Int ), d = a * m + b * n) := by
        unfold pos_com_set at d_in_poscom
        have hh := expand_poscom_set d a b
        rw[hh] at d_in_poscom
        exact d_in_poscom.left

      obtain ⟨ m, hm ⟩ := ham_d
      obtain ⟨ n, hn ⟩ := hm

      have r_eq_zero : (r = .zero) :=
        by
          apply Classical.byContradiction
          intro r_neq_zero
          have h3 := expand_poscom_set r a b
          symm at h3
          have ham_r : (∃ (m n : Int ), r = a * m + b * n) :=
            by
              exists (Int.one.negate + q * m)
              exists (q * n)
              rw[mul_add_distributes]
              apply add_right_cancel r (a * Int.one.negate + a * (q*m) + b * (q* n)) a
              rw[hq1]
              rw[sub_is_plus_neg]
              rw[int_add_associates]
              rw[inverse_nat2]
              rw[int_add_zero]
              rw[<-neg_expands_mul]
              rw[int_mul_one]
              rw[int_add_commutes]
              rw[<-int_add_associates]
              rw[<-int_add_associates]
              rw[inverse_nat]
              rw[int_zero_add]
              rw (occs := .pos [2])[int_mul_commutes]
              rw (occs := .pos [4])[int_mul_commutes]
              rw[int_mul_associates]
              rw[int_mul_associates]
              rw[<-mul_add_distributes]
              apply mul_left_congr
              rw[int_mul_commutes]
              rw (occs := .pos [2] )[int_mul_commutes]
              exact hn
          have r_gt_zero : .zero < r := by
            have hh := And.intro hq2 r_neq_zero
            simp only [(· < · )]
            unfold Int.lt
            constructor
            exact hh.left
            symm
            exact hh.right
          have r_in_a : (r ∈ pos_com_set) :=
            by
              unfold pos_com_set
              have hand := And.intro ham_r r_gt_zero
              rw[h3] at hand
              exact hand
          have d_leq_r : (d ≤ r) :=
            by
              unfold is_min at hd
              exact hd.right r r_in_a
          have d_eq_r : (d = r) :=
            by
              have hq4 := lt_means_lte r d hq3
              exact (lte_antisym r d hq4 d_leq_r).symm
          have d_neq_r : (d ≠ r) := (lt_means_neq r d hq3).symm
          contradiction

      unfold Int.Divides
      exists q
      rw[r_eq_zero] at hq1
      have hh2 : (.zero + a) = (q * d - a) + a := add_right_congr Int.zero (q * d - a) a hq1
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

      have ham_d : (∃ (m n : Int ), d = a * m + b * n) := by
        unfold pos_com_set at d_in_poscom
        have hh := expand_poscom_set d a b
        rw[hh] at d_in_poscom
        exact d_in_poscom.left

      obtain ⟨ m, hm ⟩ := ham_d
      obtain ⟨ n, hn ⟩ := hm

      have r_eq_zero : (r = .zero) :=
        by
          apply Classical.byContradiction
          intro r_neq_zero
          have h3 := expand_poscom_set r a b
          symm at h3
          have ham_r : (∃ (m n : Int ), r = a * m + b * n) :=
            by
              exists (q * m)
              exists (Int.one.negate + q * n)
              rw[mul_add_distributes]
              apply add_right_cancel r (a * (q*m) + (b * Int.one.negate + b * (q* n))) b
              rw[hq1]
              rw[sub_is_plus_neg]
              rw[int_add_associates]
              rw[inverse_nat2]
              rw[int_add_zero]
              rw[<-neg_expands_mul]
              rw[int_mul_one]
              rw[int_add_commutes]
              rw[<-int_add_associates]
              rw[<-int_add_associates]
              rw[int_add_commutes]
              rw[<-int_add_associates]
              rw(occs := .pos [3]) [int_add_commutes]
              rw[int_add_associates]
              rw[int_add_associates]
              rw[inverse_nat]
              rw[int_add_zero]
              rw (occs := .pos [2])[int_mul_commutes]
              rw (occs := .pos [4])[int_mul_commutes]
              rw[int_mul_associates]
              rw[int_mul_associates]
              rw[<-mul_add_distributes]
              apply mul_left_congr
              rw[int_mul_commutes]
              rw (occs := .pos [2] )[int_mul_commutes]
              rw[int_add_commutes]
              exact hn
          have r_gt_zero : .zero < r := by
            have hh := And.intro hq2 r_neq_zero
            simp only [(· < · )]
            unfold Int.lt
            constructor
            exact hh.left
            symm
            exact hh.right
          have r_in_a : (r ∈ pos_com_set) :=
            by
              unfold pos_com_set
              have hand := And.intro ham_r r_gt_zero
              rw[h3] at hand
              exact hand
          have d_leq_r : (d ≤ r) :=
            by
              unfold is_min at hd
              exact hd.right r r_in_a
          have d_eq_r : (d = r) :=
            by
              have hq4 := lt_means_lte r d hq3
              exact (lte_antisym r d hq4 d_leq_r).symm
          have d_neq_r : (d ≠ r) := (lt_means_neq r d hq3).symm
          contradiction
      unfold Int.Divides
      exists q
      rw[r_eq_zero] at hq1
      have hh2 : (.zero + b) = (q * d - b) + b := add_right_congr Int.zero (q * d - b) b hq1
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

    simp only [(· ∈ · )] at d_in_poscom
    unfold pos_com_set at d_in_poscom
    unfold PosLinearCombinations at d_in_poscom
    unfold LinearCombinations at d_in_poscom
    have d_lin_com := d_in_poscom.left
    simp only [(· ∈ · )] at d_lin_com
    obtain ⟨ m, hm ⟩ := d_lin_com
    obtain ⟨ n, hn ⟩ := hm
    rw[hk_a] at hn
    rw[hk_b] at hn
    have hca : (c.Divides (c * k_a * m)) := by
      unfold Int.Divides
      exists k_a * m
      rw[int_mul_associates]
    have hcb : (c.Divides (c * k_b * n)) := by
      unfold Int.Divides
      exists k_b * n
      rw[int_mul_associates]
    have hcab : (c.Divides ( c * k_a * m + c * k_b * n)) := by
      unfold Int.Divides
      exists (k_a * m + k_b * n)
      rw[mul_add_distributes]
      rw[int_mul_associates]
      rw[int_mul_associates]
    rw[<-hn] at hcab
    exact hcab

    exact lt_means_lte Int.zero d d_gt_zero


theorem all_divide_zero (a : Int) : (a.Divides Int.zero) :=
  by
    unfold Int.Divides
    exists Int.zero
    rw[int_mul_zero]

theorem divides_neg_iff (d a : Int) :
  (d.Divides a) ↔ (d.Divides a.negate) :=
  by
    constructor
    unfold Int.Divides
    intro d_divides_a
    obtain ⟨ k, hk ⟩ := d_divides_a
    exists k.negate
    rw[<-neg_expands_mul]
    have dd := drop_negate a (d*k)
    rw[<-dd] at hk

    exact hk

    unfold Int.Divides
    intro d_divides_aneg
    obtain ⟨ k, hk ⟩ := d_divides_aneg
    exists k.negate
    rw[<-neg_expands_mul]
    have dd := drop_negate a.negate (d*k)
    rw[<-dd] at hk
    rw[double_negate] at hk
    exact hk

theorem exists_gcd_b0_pos (a : Int) (h1 : a ≥ .zero) :
  ∃ (d : Int), IsGcd a .zero d :=
  by
    unfold IsGcd
    exists a

    constructor
    unfold Int.Divides
    exists .one
    rw[int_mul_one]

    constructor
    exact all_divide_zero a

    constructor
    intro c
    intro c_divides_a
    intro c_divides_zero

    exact c_divides_a

    exact h1

theorem lte_and_nonequal_means_lt (a b : Int) (h1 : a ≤ b) (h2 : a ≠ b)  :
  (a < b) :=
  by
    exact And.intro h1 h2

theorem gcd_symm ( a b d : Int) :
  (IsGcd a b d ↔ IsGcd b a d) := by
    unfold IsGcd
    constructor
    intro h1
    constructor
    exact h1.right.left
    constructor
    exact h1.left
    constructor
    intro c
    intro c_divides_b
    intro c_divides_a
    exact h1.right.right.left c c_divides_a c_divides_b
    exact h1.right.right.right

    intro h1
    constructor
    exact h1.right.left
    constructor
    exact h1.left
    constructor
    intro c
    intro c_divides_b
    intro c_divides_a
    exact h1.right.right.left c c_divides_a c_divides_b
    exact h1.right.right.right

theorem gcd_of_neg_is_gcd ( a b d : Int ) (h1 : IsGcd a b.negate d ) :
  IsGcd a b d := by
  unfold IsGcd
  unfold IsGcd at h1
  have d_divides_a := h1.left
  have d_divides_b := h1.right.left
  have c_divides_all := h1.right.right.left
  have d_geq_zero := h1.right.right.right
  constructor
  exact d_divides_a
  constructor
  have hh := divides_neg_iff d b
  rw[<-hh] at d_divides_b
  exact d_divides_b

  constructor
  intro c
  intro c_divides_a
  intro c_divides_b

  have hh := divides_neg_iff c b
  rw[hh] at c_divides_b

  have hcc := c_divides_all c c_divides_a c_divides_b
  exact hcc

  exact d_geq_zero

theorem gcd_of_neg_is_gcd_1 ( a b d : Int) (h1 : IsGcd a.negate b d ) :
  IsGcd a b d := by
    have h2 := gcd_symm a.negate b d
    rw[h2] at h1
    have h3 := gcd_of_neg_is_gcd b a d h1
    have h4 := gcd_symm b a d
    rw[h4] at h3
    exact h3

theorem gcd_of_neg_is_gcd_both ( a b d : Int ) (h1 : IsGcd a.negate b.negate d) :
  IsGcd a b d := by
    have h2 := gcd_of_neg_is_gcd a.negate b d h1
    have h3 := gcd_of_neg_is_gcd_1 a b d h2
    exact h3

theorem negative_zero_lte ( a : Int) (h1 : ¬(.zero ≤ a )) :
  (a.negate > .zero) :=
  by
    have h2 := not_lte_means_flip_lt Int.zero a h1
    have h3 := lt_means_lte a Int.zero h2
    have h4 := negate_lte a Int.zero h3
    rw[<-zero_negate] at h4
    by_cases h: a=.zero
    rw[h] at h1
    contradiction

    apply negative_zero_lte_from_lt
    exact h2

theorem lte_self ( a : Int ) : (a ≤ a) :=
  by
    have h1 : (a = a) := Eq.refl a
    exact eq_means_leq a a h1

theorem exists_gcd_b0_neg (a : Int) (ha : a < .zero) :
  ∃ ( d : Int), IsGcd a .zero d :=
  by
    have h0 : (Int.zero ≥ .zero) := lte_self Int.zero
    have hh : (a.negate > .zero) := negative_zero_lte_from_lt a ha
    have hh3 : (∃ (d : Int), IsGcd .zero (a.negate) d ) := by
      exact exists_gcd_pos .zero a.negate h0 hh
    obtain ⟨d, hd ⟩ := hh3
    have hd' := gcd_symm Int.zero a.negate d
    rw[hd'] at hd
    have hh := gcd_of_neg_is_gcd_1 a .zero d hd
    exists d

theorem exists_gcd_b0 (a : Int) :
  ∃ (d : Int), IsGcd a .zero d :=
  by
    by_cases ha0 : a < Int.zero
    exact exists_gcd_b0_neg a ha0

    have hh : (Int.zero ≤ a) := not_lt_means_flip_lte a Int.zero ha0
    exact exists_gcd_b0_pos a hh

theorem exists_gcd (a b : Int):
  ∃ (d : Int), IsGcd a b d :=
  by
    by_cases hb0 : Int.zero = b
    rw[<-hb0]
    exact exists_gcd_b0 a

    by_cases ha0 : Int.zero = a
    rw[<-ha0]
    have gcd_flip := exists_gcd_b0 b
    obtain ⟨ d, hd ⟩ := gcd_flip
    have hh := gcd_symm Int.zero b d
    exists d
    rw[hh]
    exact hd

    by_cases ha : Int.zero ≤ a
    by_cases hb : Int.zero ≤ b
    have hb_gt_zero : (.zero < b) := lte_and_nonequal_means_lt Int.zero b hb hb0
    exact exists_gcd_pos a b ha hb_gt_zero

    have hh := not_lte_means_flip_lt Int.zero b hb
    have hh2 : (b.negate > .zero) := negative_zero_lte b hb

    have hh3 : (∃ (d : Int), IsGcd a (b.negate) d) := by
      exact exists_gcd_pos a b.negate ha hh2
    obtain ⟨ d, hd ⟩ := hh3
    exists d
    apply gcd_of_neg_is_gcd a b d
    exact hd

    by_cases hb : Int.zero ≤ b
    have hh : (a.negate > .zero) := negative_zero_lte a ha
    have hbz : (b > .zero) := by
      have hx := And.intro hb hb0
      exact hx
    have hh3 : (∃ (d : Int), IsGcd (a.negate) b d ) := by
      exact exists_gcd_pos a.negate b (lt_means_lte .zero a.negate hh) hbz
    obtain ⟨ d, hd ⟩ := hh3
    exists d
    apply gcd_of_neg_is_gcd_1 a b d
    exact hd

    have hha : (a.negate > .zero) := negative_zero_lte a ha
    have hhb : (b.negate > .zero) := negative_zero_lte b hb
    have hh3 : (∃ (d : Int), IsGcd (a.negate) (b.negate) d ) := by
      exact exists_gcd_pos a.negate b.negate (lt_means_lte .zero a.negate hha) hhb
    obtain ⟨ d, hd ⟩ := hh3
    exists d
    have hd2 := gcd_of_neg_is_gcd_both a b d hd
    exact hd2

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


theorem common_div_divides_gcd ( a b d : Int )
  (h1:  d.Divides a)
  (h2 : d.Divides b) :
  (d.Divides (Int.gcd a b)) :=
  by
    have hg := gcd_is_gcd a b
    unfold IsGcd at hg
    have h3 := hg.right.right.left d h1 h2
    exact h3

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
