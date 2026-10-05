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

theorem zero_not_divisor (a b : Int) (h1 : a.Divides b)  (h2 : b ≠ .zero): a ≠ .zero :=
  by
    intro a_eq_zero
    rw[a_eq_zero] at h1
    dsimp [Int.Divides] at h1
    obtain ⟨ k, hk ⟩ := h1
    simp at hk
    contradiction

theorem intofnat_geq_zero (a : Nat) : intOfNat a ≥ .zero := rfl

theorem one_neq_zero : Int.one ≠ Int.zero := by
  intro h1
  rw[Int.one, Int.zero] at h1
  have h2 := intofnat_eq MyNat.Nat.one MyNat.Nat.zero h1
  contradiction

theorem natplus_means_gte (a b : Int) (n : Nat) (h1: a = intOfNat n + b) : a ≥ b :=
  by
    have h2 := intofnat_geq_zero n
    have h3 := lte_add_right Int.zero (intOfNat n) b h2
    rw[<-h1] at h3
    simp at h3
    exact h3

theorem lt_lte_trans (a b c : Int) (h1 : a < b) (h2 : b ≤ c) : a < c :=
  by
    simp only [(· < ·  )]
    have h3 := lt_means_lte a b h1
    dsimp [Int.lt]
    constructor
    exact lte_trans a b c h3 h2

    intro h4
    rw[h4] at h3
    have h5 := lte_antisym b c h2 h3
    rw[h4] at h1
    rw[h5] at h1
    have h6 := lt_means_neq c c h1
    contradiction

theorem lt_trans (a b c : Int) (h1 : a < b) (h2 : b < c) : (a < c) :=
  by
    have h3 := lt_means_lte b c h2
    exact lt_lte_trans a b c h1 h3

theorem intofnat_succ (a : Nat) : (intOfNat a.succ = intOfNat a + .one) :=
  by
    rw[Int.one]
    rw[<-add_mk_nat]
    apply intofnat_eq_rev
    rw[MyNat.succ_add_one]

theorem nat_cancel_both_sides (a b : Nat) (h1 : a = a + b) : b = .zero :=
  by
    have h2 : .zero + a = a + b := by
      have h2 := MyNat.zero_add a
      rw (occs := .pos [1]) [<-h2] at h1
      exact h1
    rw[add_commutes] at h2
    have h3 := MyNat.add_left_cancel MyNat.Nat.zero b a h2
    exact h3.symm

theorem one_lt_two : Int.one < Int.two := by
  rw[Int.one, Int.two]
  apply intofnat_lt_equiv
  dsimp [MyNat.Nat.lt]
  constructor
  rfl
  rw[MyNat.Nat.two]
  rw[MyNat.succ_add_one]
  intro h1
  have h2 := nat_cancel_both_sides MyNat.Nat.one MyNat.Nat.one h1
  contradiction

theorem neq_sym (a b :Int) (h1 : ¬ (a = b)) : a ≠ b := by
  simp
  exact h1


theorem div_means_neg_div ( a b : Int) (h1 : a.Divides b ) : a.negate.Divides b :=
  by
    dsimp [Int.Divides]
    dsimp [Int.Divides] at h1
    obtain ⟨ k, hk ⟩ := h1
    exists (k.negate)
    rw[<-neg_expands_mul]
    rw[int_mul_commutes]
    rw[<-neg_expands_mul]
    simp
    rw[int_mul_commutes]
    exact hk

theorem flip_negate_eq ( a b : Int) (h1 : a.negate = b) : a = b.negate :=
  by
    have h2 := negate_both_sides a.negate b h1
    simp at h2
    exact h2

theorem lt_self_means_false (a : Int) (h1 : a < a) : False :=
  by
    have h2 := lt_means_neq a a h1
    contradiction

theorem negate_lt (a b : Int) (h1 : a < b) : b.negate < a.negate := by
  have h2 := lt_means_lte a b h1
  have h3 := negate_lte a b h2

  simp only [(· < ·)]
  dsimp [Int.lt]
  constructor
  exact h3

  intro h4
  have h5 : b = a := unnegate_both b a h4
  symm at h5
  have h6 := lt_means_neq a b h1
  contradiction

theorem div_means_lte (a b : Int) (b_gt_zero : b > .zero) (h1 : a.Divides b) : a ≤ b := by
  dsimp [Int.Divides] at h1
  obtain ⟨ k, hk ⟩ := h1
  rw[hk]
  rw[hk] at b_gt_zero
  by_cases a_zeroness : a = .zero

  rw[a_zeroness]
  simp
  rfl
  by_cases a_sign : a >= .zero
  have h1 := prod_geq_means_op_geq a k (lt_means_lte Int.zero (a*k) b_gt_zero) a_sign a_zeroness

  by_cases hk0 : k = .zero
  rw[hk0] at hk
  simp at hk

  rw[hk0] at b_gt_zero
  simp at b_gt_zero
  have h2 := lt_self_means_false Int.zero b_gt_zero
  contradiction

  have one_lte_k : .one ≤ k := by
    have h0 := neq_sym k Int.zero hk0
    have h2 : .zero < k := And.intro h1 h0.symm
    have h3 := zero_lt_means_one_lte k h2
    exact h3
  have h2 := int_lte_mul_left .one k a one_lte_k a_sign
  simp at h2
  rw[int_mul_commutes] at h2
  exact h2

  have a_sign2 := not_lte_means_flip_lt Int.zero a a_sign
  rw[<-hk] at b_gt_zero
  have h3 := lt_trans a Int.zero b a_sign2 b_gt_zero
  rw[<-hk]
  exact lt_means_lte a b h3

theorem pos_divs_of_one (a : Int) (h1 : a ≥ .zero) (h2 : a.Divides .one) :
  a = .one := by
    have anat := nonneg_is_nat a h1
    obtain ⟨ k, hk ⟩ := anat
    cases k with
    | zero =>
      have h3 := zero_not_divisor a Int.one h2 one_neq_zero
      contradiction
    | succ k =>
      cases k with
      | zero =>
        rw[<-MyNat.Nat.one] at hk
        rw[<-Int.one] at hk
        exact hk
      | succ k =>
        rw[intofnat_succ] at hk
        rw[intofnat_succ] at hk
        simp at hk
        have a_geq_two := natplus_means_gte a Int.two k hk
        have h4 := lt_lte_trans Int.one Int.two a one_lt_two a_geq_two
        have a_lte_one := div_means_lte a Int.one zero_lt_one h2
        have h5 := lt_and_lte_means_false Int.one a  a_lte_one h4
        contradiction

theorem divs_of_one (a : Int) (h1 : a.Divides Int.one) : a = .one ∨ a = Int.one.negate :=
  by
    by_cases a_sign : a ≥ .zero
    left
    exact pos_divs_of_one a a_sign h1

    right
    have a_lte_zero := lt_means_lte a Int.zero (not_lte_means_flip_lt Int.zero a a_sign)
    have a_neg_sign := negate_lte a Int.zero a_lte_zero
    simp at a_neg_sign
    have h2 := div_means_neg_div a Int.one h1
    have h3 := pos_divs_of_one a.negate a_neg_sign h2
    exact flip_negate_eq a Int.one h3

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

theorem gcd_means_isgcd (a b d : Int) (h1 : d = Int.gcd a b) : IsGcd a b d :=
  by
    have h2 := gcd_is_gcd a b
    rw[<-h1] at h2
    exact h2

theorem cancel_to_one ( a b : Int) (h1 : a = a * b) (h2 : a ≠ .zero ) : b = .one :=
  by
    have h3 := int_mul_one a
    rw[<-h3] at h1
    rw[int_mul_associates] at h1
    have h4 := mul_left_divides Int.one (Int.one * b) a h1 h2
    simp at h4
    exact h4.symm

theorem both_divide_pos ( a b : Int ) (h1 : a.Divides b) (h2 : b.Divides a) (a_gte_zero : a ≥ .zero) (b_gte_zero : b ≥ .zero) : a = b :=
  by
    by_cases h0 : b = .zero

    rw[h0] at h1
    rw[h0] at h2

    dsimp [Int.Divides] at h2
    obtain ⟨ k, hk ⟩ := h2
    simp at hk
    rw[hk]
    rw[h0]

    dsimp [Int.Divides] at h1
    dsimp [Int.Divides] at h2
    obtain ⟨k1, hk1⟩ := h1
    obtain ⟨ k2, hk2⟩ := h2
    rw[hk2] at a_gte_zero
    have k2_geq_zero := prod_geq_means_op_geq b k2 a_gte_zero b_gte_zero h0
    rw[<-hk2] at a_gte_zero

    rw[hk2] at hk1
    rw[int_mul_associates] at hk1
    have h3 := cancel_to_one b (k2 * k1) hk1 h0
    have k1_div_one := prod_means_div_right k2 k1 Int.one h3
    have k2_div_one := prod_means_div_left k2 k1 Int.one h3
    rw[<-Int.Unit] at k1_div_one
    rw[<-Int.Unit] at k2_div_one

    have k1_unit := unit_means_one_or_negone k1 k1_div_one
    have k2_unit := unit_means_one_or_negone k2 k2_div_one

    by_cases hkx : k2 = Int.one.negate
    rw[hkx] at k2_geq_zero
    contradiction

    have hk_one := Or.elim k2_unit.symm hkx
    simp at hk_one

    rw[hk_one] at h3
    simp at h3

    rw[hk_one] at hk2
    simp at hk2
    exact hk2

theorem divides_neg_both ( a b : Int) (h1: a.Divides b) : a.negate.Divides b.negate :=
  by
    apply div_means_neg_div
    apply divides_neg
    exact h1

theorem both_divide_means_associates (a b : Int) (h1 : a.Divides b) (h2: b.Divides a) : a = b ∨ a = b.negate :=
  by
    by_cases a_sign : a >= .zero
    by_cases b_sign : b >= .zero
    left
    exact both_divide_pos a b h1 h2 a_sign b_sign

    have b_flip := not_lte_means_flip_lt Int.zero b b_sign
    right
    have bneg_sign := (lt_means_lte Int.zero b.negate (negate_lt b Int.zero b_flip))
    exact both_divide_pos a b.negate (divides_neg a b h1) (div_means_neg_div b a h2) a_sign bneg_sign

    have a_flip := not_lte_means_flip_lt Int.zero a a_sign
    have aneg_sign := (lt_means_lte Int.zero a.negate (negate_lt a Int.zero a_flip))
    by_cases b_sign : b >= .zero

    right
    have h4 := both_divide_pos a.negate b (div_means_neg_div a b h1) (divides_neg b a h2) aneg_sign b_sign
    apply unnegate_both
    simp
    exact h4

    left
    have b_flip := not_lte_means_flip_lt Int.zero b b_sign
    have bneg_sign := (lt_means_lte Int.zero b.negate (negate_lt b Int.zero b_flip))
    have h5 := both_divide_pos a.negate b.negate (divides_neg_both a b h1) (divides_neg_both b a h2) aneg_sign bneg_sign
    apply unnegate_both
    exact h5

theorem gcd_pos (a b d : Int) (h1 : IsGcd a b d) : d ≥ .zero := by
  dsimp [IsGcd] at h1
  exact h1.right.right.right

theorem gcd_unique ( a b c d : Int) (h1 : IsGcd a b c) (h2 : IsGcd a b d) : c = d := by
  dsimp [IsGcd] at h1
  dsimp [IsGcd] at h2
  have c_gte_zero := gcd_pos a b c h1
  have d_gte_zero := gcd_pos a b d h2

  have h3 := h1.right.right.left d h2.left h2.right.left
  have h4 := h2.right.right.left c h1.left h1.right.left
  have h5 := both_divide_means_associates c d h4 h3

  apply Classical.byContradiction
  intro h6
  have h7 := Or.elim h5 h6
  simp at h7
  have h8 := negate_lte Int.zero d d_gte_zero
  simp at h8
  rw[<-h7] at h8
  have h9 := lte_antisym c Int.zero h8 c_gte_zero
  rw[h9] at h7
  have h8 := negate_both_sides Int.zero d.negate h7
  simp at h8
  rw[<-h9] at h8
  contradiction

theorem isgcd_means_gcd (a b d : Int) (h1 : IsGcd a b d) : a.gcd b = d :=
  by
    have h2 := gcd_is_gcd a b
    have h3 := gcd_unique a b (a.gcd b) d h2 h1
    exact h3


theorem gcd_left_zero_zero (a : Int) (h1 : Int.gcd .zero a = .zero)  : a = .zero :=
  by
    have h2 := gcd_means_isgcd Int.zero a Int.zero h1.symm
    dsimp [IsGcd] at h2
    have h3 := h2.right.left
    dsimp [Int.Divides] at h3
    obtain ⟨ k, hk ⟩ := h3
    simp at hk
    exact hk

theorem gcd_fn_symm (a b : Int) : a.gcd b = b.gcd a := by
  let d := a.gcd b
  have hd : d = a.gcd b := rfl
  have h1 := gcd_means_isgcd a b d hd
  have hx := (gcd_symm a b d).mp h1
  have h2 := isgcd_means_gcd b a d hx
  rw[hd] at h2
  exact h2.symm

theorem gcd_right_zero_zero (a : Int) (h1 : Int.gcd a .zero = .zero)  : a = .zero := by
  have h2 := gcd_fn_symm a Int.zero
  rw[h2] at h1
  exact gcd_left_zero_zero a h1

theorem gcd_means_divides (a b d : Int) (h1 : Int.gcd a b = d) :  d.Divides a ∧ d.Divides b :=
  by
    have h2 := gcd_means_isgcd a b d h1.symm
    exact And.intro (h2.left) (h2.right.left)

theorem gcd_zero_means_both_zero (a b : Int) (h1 : Int.gcd a b = .zero) : a = .zero ∧ b = .zero :=
  by
    by_cases a_sign : a = Int.zero
    constructor
    exact a_sign
    rw[a_sign] at h1
    exact gcd_left_zero_zero b h1

    have h2 := gcd_means_divides a b Int.zero h1
    have h3 := zero_not_divisor Int.zero a h2.left (neq_sym a Int.zero a_sign)
    contradiction


theorem neg_one_lt_zero : Int.one.negate < .zero := by
  have h1 := zero_lt_one
  have h2 := negate_lt Int.zero Int.one h1
  simp at h2
  exact h2

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
    have h11 : d > .zero := sorry

    have h12 : d = .one ∨ d = .two := pos_divisors_of_two d h11 h9
    exact h12

end MyInt
