import Project1.Integers.Inequalities
import Project1.Integers.Arithmetic
import Project1.Nat.Parity


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
              sorry
          have hx4 : (k + Int.one.negate < Int.one.negate) := sorry

          sorry
      simp at hk3

      sorry
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
    sorry

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


    sorry

    sorry

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

theorem even_means_two_divides (a : Int ) (h1 : Int.Even a) : Int.two.Divides a :=
  by
    unfold Int.Even at h1
    exact h1


end MyInt
