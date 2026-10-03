import Project1.Integers.Inequalities
import Project1.Integers.Arithmetic
import Project1.Nat.Parity
import Project1.Integers.Gcd


namespace MyInt


theorem even_or_odd_nat ( a : Nat ) : (MyNat.Nat.Even a ∨  MyNat.Nat.Odd a) :=
  by
    induction a with
    | zero =>
      left
      unfold MyNat.Nat.Even
      unfold MyNat.Nat.Divides
      exists .zero
    | succ a ih =>
      by_cases h: a.Even
      right
      unfold MyNat.Nat.Even at h
      unfold MyNat.Nat.Divides at h
      obtain ⟨ k, hk ⟩ := h
      unfold MyNat.Nat.Odd
      exists k
      rw[MyNat.add_one]
      rw[add_commutes]
      apply MyNat.add_right_congr
      exact hk

      left
      have h2 := ih.resolve_left h
      unfold MyNat.Nat.Odd at h2
      unfold MyNat.Nat.Even
      unfold MyNat.Nat.Divides
      obtain ⟨ k, hk ⟩ := h2
      exists ( k + .one )
      rw[MyNat.add_one]
      rw[add_commutes]
      rw[MyNat.mul_add_distributes]
      rw[MyNat.mul_one]
      rw (occs := .pos [2]) [MyNat.Nat.two]
      rw[MyNat.add_one]
      rw[<-MyNat.add_associates]
      apply MyNat.add_right_congr
      exact hk

theorem eq_means_intofnat_eq ( a b : Nat ) ( h1 : a = b ) : (intOfNat a = intOfNat b) :=
  by
    unfold intOfNat
    unfold intOfRep
    apply Quotient.sound
    apply unfold_intrep_equiv_congr
    dsimp [IntRep.Equivalent]
    rw[MyNat.add_zero, MyNat.add_zero]
    exact h1

theorem intofnat_geq_zero ( a : Nat ) : (.zero ≤ intOfNat a) :=
  by
    induction a with
    | zero =>
    rw[Int.zero]
    rfl
    | succ a ih =>
    let b : Int := intOfNat a
    have h2 := int_nat_succ a b rfl
    rw[<-h2]
    have h3 : (b ≤ b + .one) := by
      have h4 := lte_add_right Int.zero Int.one b rfl
      rw[int_add_commutes]
      rw[int_zero_add] at h4
      exact h4
    unfold b at h3
    unfold b
    have h4 := lte_trans Int.zero (intOfNat a) (intOfNat a + Int.one) ih h3
    exact h4

theorem parity_iff_nat_even (a : Nat) : Int.Even (intOfNat a) ↔ MyNat.Nat.Even a :=
  by
    constructor

    intro h1
    unfold Int.Even at h1
    unfold Int.Divides at h1
    obtain ⟨ k, hk ⟩ := h1
    unfold MyNat.Nat.Even
    unfold MyNat.Nat.Divides
    have hk_geq : (k ≥ Int.zero) := by
      have hk_zero : (.zero ≤ Int.two * k) := by
        have h2 := intofnat_geq_zero a
        rw[hk] at h2
        exact h2
      have h3 := prod_geq_means_op_geq Int.two k hk_zero zero_leq_two two_neq_zero
      exact h3
    have exists_nat := nonneg_is_nat k hk_geq
    obtain ⟨ m, hm ⟩ := exists_nat
    exists m
    rw[Int.two] at hk
    rw[hm] at hk
    rw[<-mul_mk_nat] at hk
    have hk2 := intofnat_eq a (MyNat.Nat.two * m) hk
    exact hk2

    intro h1
    unfold MyNat.Nat.Even at h1
    unfold MyNat.Nat.Divides at h1
    obtain ⟨ k, hk ⟩ := h1
    unfold Int.Even
    unfold Int.Divides
    exists (intOfNat k)

    rw[Int.two]
    rw[<-mul_mk_nat]
    exact eq_means_intofnat_eq a (MyNat.Nat.two * k) hk

theorem nothing_between_zero_one (a : Int) (h1 : a > .zero) (h2 : a < .one) : False :=
  by
    have h3 := lt_means_lte Int.zero a h1
    have h4 := nonneg_is_nat a h3
    obtain ⟨ k, hk ⟩ := h4
    rw[hk] at h1
    rw[hk] at h2
    rw[Int.one] at h2
    rw[Int.zero] at h1
    have h4 := intofnat_lt_equiv_rev k MyNat.Nat.one h2
    have h5 := intofnat_lt_equiv_rev MyNat.Nat.zero k h1

    have h6 := MyNat.lt_means_neq MyNat.Nat.zero k h5
    symm at h6
    have h7 := MyNat.lt_one_means_eq_zero k h4
    contradiction

theorem lt_means_lte_plus_one (a b : Int) (h1 : a < b) : a + .one ≤ b :=
  by
    rw[Int.one, intOfNat]
    have h2 := exists_intofrep a
    obtain ⟨ ak, hak ⟩ := h2
    have h3 := exists_intofrep b
    obtain ⟨ bk, hbk ⟩ := h3

    rw[hak, hbk] at h1
    rw[hak, hbk]
    rw[<-add_mk]
    simp
    apply intofrep_leq_rev
    simp
    have h2 := lt_means_lte (intOfRep ak) (intOfRep bk) h1
    have h3 := intofrep_leq ak bk h2
    have h4 := lt_means_neq (intOfRep ak) (intOfRep bk) h1
    rw[add_associates]
    rw (occs := .pos [2]) [add_commutes]
    rw[<-MyNat.succ_add_one]
    rw[MyNat.succ_add]
    have h5 : (ak.pos + bk.neg ≠ bk.pos + ak.neg) :=
      by
        intro h5
        have h6 := intofrep_eq_rev ak bk h5
        contradiction
    have h6 : (ak.pos + bk.neg < bk.pos + ak.neg) := And.intro h3 h5
    have h7 := MyNat.lt_means_succ_lte (ak.pos + bk.neg) (bk.pos + ak.neg) h6
    exact h7

theorem gt_neg_one_means_geq_zero (a : Int) (h1 : a > Int.one.negate) : a ≥ .zero :=
  by
    have h2 := lt_means_lte_plus_one Int.one.negate a h1
    simp at h2
    exact h2

theorem odd_neq_even (a b : Int) (h1: Int.Odd a) (h2: Int.Even b) :
    (a ≠ b) := by
      dsimp [Int.Odd] at h1
      dsimp [Int.Even, Int.Divides] at h2
      obtain ⟨ k, hk ⟩ := h1
      obtain ⟨ m, hm ⟩ := h2
      intro a_eq_b
      rw[hm, hk] at a_eq_b
      have h3 := add_right_congr (Int.two * k + Int.one) (Int.two * m) (Int.two * k).negate a_eq_b
      rw[int_add_commutes] at h3
      rw[<-int_add_associates] at h3
      simp at h3
      rw[neg_expands_mul] at h3
      rw[<-mul_add_distributes] at h3
      have h4 : (Int.two.Divides Int.one) :=
        by
          unfold Int.Divides
          exists (m + k.negate)
      have h5 := one_is_unit Int.two h4 zero_lt_two
      have h6 := int_two_neq_one
      contradiction

theorem parity_iff_nat_odd (a : Nat) : Int.Odd (intOfNat a) ↔ MyNat.Nat.Odd a :=
  by
    constructor
    intro h1
    dsimp [Int.Odd] at h1
    obtain ⟨ k, hk ⟩ := h1
    dsimp [MyNat.Nat.Odd]
    have hk2 : (k ≥ .zero) := by
      have nata_geq_zero := intofnat_geq_zero a
      rw[hk] at nata_geq_zero
      have hk3 : (Int.zero + Int.one.negate ≤ Int.two * k + Int.one + Int.one.negate) :=
        by
          simp
          by_cases hx : k ≥ .one
          have hx2 := int_lte_mul_left Int.one k Int.two hx rfl
          simp at hx2

          have hx3 : Int.two ≥ .zero := by rfl
          have hx4 : Int.one.negate ≤ .zero := by rfl
          have hx5 : Int.one.negate ≤ Int.two := by rfl

          have k_geq_zero : (k ≥ .zero) := by
            exact lte_trans Int.zero Int.one k rfl hx

          have k_neq_zero : (k ≠ .zero) := by
            intro hno
            rw[hno] at hx
            contradiction
          have hx6 := int_lte_mul_left Int.one.negate Int.two k hx5 k_geq_zero
          have hx8 : (Int.two * k ≥ .zero) := by
            have hx9 := geq_zero_means_prod_geq Int.two k rfl k_geq_zero k_neq_zero
            exact lte_trans Int.zero Int.two (Int.two * k) rfl hx9
          exact lte_trans Int.one.negate .zero (Int.two*k) hx4 hx8

          by_cases hx2 : k = .zero
          rw[hx2]
          simp
          rfl

          have hx3 : (k < .zero) :=
            by
              simp only [(· < · )]
              dsimp [Int.lt]
              constructor
              apply Classical.byContradiction
              intro hx3
              have hx4 := not_lte_means_flip_lt k Int.zero hx3
              have hx2 := not_lte_means_flip_lt Int.one k hx
              exact nothing_between_zero_one k hx4 hx2
              exact hx2

          have hx4 : (.two * k < .zero) := by
            have hx5 : Int.two > .zero := by
              simp only [(· > · )]
              simp only [(· < · )]
              dsimp [Int.lt]
              constructor
              rfl
              intro hx4
              have hx5 := two_neq_zero
              symm at hx4
              contradiction
            exact lte_nonneg_neg Int.two k hx5 hx3
          have hx5 : (.two * k + .one < .one) := lt_add_right (.two * k)  .zero .one  hx4
          have hx6 : (.two * k + .two ≤ .one) := by
            have hx7 := lt_means_lte_plus_one (.two * k + .one) (.one) hx5
            rw[int_add_associates] at hx7
            simp at hx7
            exact hx7
          have hx7 : (.two * k + .one ≤ .zero) := by
            have hx7 := lte_add_right (Int.two * k + Int.two) Int.one Int.one.negate hx6
            simp at hx7
            rw[int_add_associates] at hx7
            simp at hx7
            exact hx7
          have hx8 := lte_antisym (.two * k + .one) .zero hx7 nata_geq_zero
          have hx9 : (Int.Odd (Int.two * k + Int.one)) := by
            dsimp [Int.Odd]
            exists k
          have hx10 : (Int.Even (Int.zero)) := by
            unfold Int.Even
            unfold Int.Divides
            exists Int.zero
          have hx11 := odd_neq_even (Int.two *k + Int.one)  (Int.zero) hx9 hx10
          contradiction
      simp at hk3

      have hk4 : (k > Int.one.negate) :=
        by
          apply Classical.byContradiction
          intro hk4
          have hk5 := not_lt_means_flip_lte Int.one.negate k hk4
          have hk6 := int_lte_mul_left k Int.one.negate Int.two hk5 rfl
          rw[int_mul_commutes] at hk6
          have hk7 := lte_add_right (Int.two * k) (Int.one.negate * Int.two) Int.one hk6
          rw (occs := .pos [2]) [int_mul_commutes] at hk7
          rw[<-negate_to_mul_neg_one] at hk7

          have hk_rhs : (Int.two.negate + Int.one = Int.one.negate ) :=
            by
              apply add_right_cancel (c := Int.one.negate)
              simp
              have hn1 : (Int.two = Int.one + Int.one) := rfl
              have hn2 := negate_both_sides Int.two (Int.one + Int.one) hn1
              exact hn2
          rw[hk_rhs] at hk7


          have hk8 : (Int.two * k + Int.one < Int.zero) :=
            by
              simp only [(· < · )]
              dsimp [Int.lt]
              constructor
              exact lte_trans (Int.two * k + Int.one) Int.one.negate Int.zero  hk7 rfl
              intro hk8
              rw[hk8] at hk7
              contradiction

          exact lt_and_lte_means_false (Int.two * k + Int.one) Int.zero nata_geq_zero  hk8

      exact gt_neg_one_means_geq_zero k hk4
    have exists_knat := nonneg_is_nat k hk2
    obtain ⟨knat, hknat⟩ := exists_knat
    exists knat
    apply intofnat_eq
    rw[add_mk_nat]
    rw[<-Int.one]
    rw[mul_mk_nat]
    rw[<-Int.two]
    rw[<-hknat]
    exact hk

    dsimp [Int.Odd]
    intro h1
    dsimp [MyNat.Nat.Odd] at h1
    obtain ⟨ knat , hknat ⟩ := h1
    exists intOfNat knat
    rw[Int.two]
    rw[<-mul_mk_nat]
    rw[Int.one]
    rw[<-add_mk_nat]
    apply intofnat_eq_rev
    exact hknat

theorem parity_iff_negate_even (a : Int):  (Int.Even a) ↔ Int.Even a.negate :=
  by
    dsimp [Int.Even, Int.Divides]
    constructor
    intro h1
    obtain ⟨ k, hk ⟩ := h1
    exists k.negate
    rw[<-neg_expands_mul]
    apply negate_both_sides
    exact hk

    intro h1
    obtain ⟨ k, hk ⟩ := h1
    exists k.negate
    rw[<-neg_expands_mul]
    apply unnegate_both
    simp
    exact hk

theorem intofrep_plus (a b : IntRep) :
  (a + b = IntRep.mk (a.pos + b.pos) (a.neg + b.neg)) :=
    by
      rfl

theorem one_minus_two_is_neg_one : (Int.one - Int.two = Int.one.negate) :=
  by
    rw[sub_is_plus_neg]
    rw [Int.one]
    rw [Int.two]
    rw [intOfNat, intOfNat]
    rw[<-negate_mk]
    rw[<-negate_mk]
    rw[<-add_mk]
    rw[intofrep_plus]
    simp
    dsimp [IntRep.negate]
    simp
    apply intofrep_eq_rev
    simp
    rw[<-MyNat.add_one]
    rw[<-MyNat.Nat.two]

theorem int_neg_expands (a b : Int) : a.negate + b.negate = (a+b).negate :=
  by
    have h1 := exists_intofrep a
    have h2 := exists_intofrep b

    obtain ⟨ ak, hak ⟩ := h1
    obtain ⟨ bk, hkb ⟩ := h2
    rw[hak, hkb]
    rw[<-negate_mk]
    rw[<-negate_mk]
    rw[<-add_mk]
    simp
    cases ak with
    | mk akpos akneg =>
    cases bk with
    | mk bkpos bkneg =>
    rw[<-add_mk]
    simp
    dsimp [IntRep.negate]
    rfl

theorem parity_iff_negate_odd (a : Int):  (Int.Odd a) ↔ Int.Odd a.negate :=
  by
    constructor

    intro a_odd
    dsimp [Int.Odd] at a_odd
    dsimp [Int.Odd]
    obtain ⟨ k, hk ⟩ := a_odd

    exists (k.negate + Int.one.negate)
    rw[mul_add_distributes]
    rw[<-negate_to_mul_neg_one]
    rw[int_add_associates]
    rw (occs := .pos [2]) [int_add_commutes]
    rw[<-sub_is_plus_neg]

    rw[one_minus_two_is_neg_one]
    rw[<-neg_expands_mul]
    rw[int_neg_expands]
    apply negate_both_sides
    exact hk

    intro a_odd
    dsimp [Int.Odd] at a_odd
    dsimp [Int.Odd]
    obtain ⟨ k, hk ⟩ := a_odd

    exists (k.negate + Int.one.negate)
    rw[mul_add_distributes]
    rw[<-negate_to_mul_neg_one]
    rw[int_add_associates]
    rw (occs := .pos [2]) [int_add_commutes]
    rw[<-sub_is_plus_neg]

    rw[one_minus_two_is_neg_one]
    rw[<-neg_expands_mul]
    rw[int_neg_expands]
    apply unnegate_both
    simp
    exact hk

theorem even_or_odd (a : Int) : (Int.Even a ∨ Int.Odd a) :=
  by
    by_cases hh : (a ≥ .zero)
    have h1 := nonneg_is_nat a hh
    obtain ⟨ k, hk ⟩ := h1
    rw[hk]

    rw[parity_iff_nat_even]
    rw[parity_iff_nat_odd]
    exact (MyNat.odd_or_even k).symm

    have h2 := not_lte_means_flip_lt Int.zero a hh
    have h3 := negative_zero_lte_from_lt a h2
    have h1 := nonneg_is_nat a.negate (lt_means_lte Int.zero a.negate h3)
    obtain ⟨ k, hk ⟩ := h1

    rw[parity_iff_negate_odd]
    rw[parity_iff_negate_even]
    rw[hk]
    rw[parity_iff_nat_even]
    rw[parity_iff_nat_odd]
    exact (MyNat.odd_or_even k).symm

theorem not_even_means_odd (a : Int ) (h1 : ¬ Int.Even a) : Int.Odd a :=
  by
    have h2 := even_or_odd a
    have h3 := Or.elim h2 h1
    simp at h3
    exact h3

theorem even_means_not_odd (a : Int) : (Int.Even a) →  (¬ Int.Odd a ) :=
  by
    intro h1
    have h2 : (a = a) := rfl
    intro h3
    have h4 : (a ≠ a) := odd_neq_even a a h3 h1
    contradiction

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
    have h10 : (Int.two = Int.one) := one_is_unit .two h9 zero_lt_two
    have h12 := And.intro h10 int_two_neq_one
    simp at h12

end MyInt
