import Project1.Integers.Inequalities
import Project1.Integers.Arithmetic

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
      have h4 := lte_add_right Int.one Int.zero b rfl
      rw[int_add_commutes]
      rw[int_zero_add] at h4
      exact h4
    unfold b at h3
    unfold b
    have h4 := lte_trans Int.zero (intOfNat a) (intOfNat a + Int.one) ih h3
    exact h4

theorem parity_iff_nat (a : Nat) : Int.Even (intOfNat a) ↔ MyNat.Nat.Even a :=
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

theorem even_or_odd_intofnat (a : Nat) : (Int.Even (intOfNat a)) ∨ (Int.Odd (intOfNat a)) :=
  by
    sorry

theorem even_or_odd (a : Int) : (Int.Even a ∨ Int.Odd a) :=
  by
    by_cases h1: Int.Even a
    left
    exact h1

    right
    unfold Int.Odd
    unfold Int.Even at h1
    apply Classical.byContradiction
    intro h2

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

theorem even_means_two_divides (a : Int ) (h1 : Int.Even a) : Int.two.Divides a :=
  by
    unfold Int.Even at h1
    exact h1


end MyInt
