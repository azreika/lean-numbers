import Project1.Integers.Arithmetic
import Project1.IntReps.Inequalities
import Project1.Nat.Properties

import Std

namespace MyInt

def Int.lte : Int -> Int -> Prop :=
  Quotient.lift₂
    IntRep.lte
    (by
      intro a1 b1 a2 b2
      intro h1 h2

      have h3 : (a1.lte b1 = a1.lte b2) := lte_respects_right a1 b1 b2 h2
      have h4 : (a1.lte b2 = a2.lte b2) := lte_respects_left a1 a2 b2 h1
      have h5 : (a1.lte b1 = a2.lte b2) := Eq.trans h3 h4
      exact h5
    )

instance : LE IntRep where
  le := IntRep.lte
instance : LE Int where
  le := Int.lte

def Int.lt (a b : Int) : Prop :=
  a ≤ b ∧ a ≠ b

instance : LT Int where
  lt := Int.lt

theorem lte_symbol (a b : Int ) (h1 : a ≤ b) : (a.lte b) :=
  by exact h1

theorem lte_symbol_rev (a b : Int ) (h1 : a.lte b) : (a ≤ b) :=
  by exact h1


theorem intrep_leq (a b : IntRep ) (h1: a ≤ b) : (a.pos + b.neg ≤ b.pos + a.neg) := h1

theorem intofrep_leq ( a b : IntRep ) (h1 : intOfRep a ≤  intOfRep b):
  (a.pos + b.neg ≤  b.pos + a.neg) := h1

theorem intofrep_leq_rev ( a b : IntRep )
  (h1: a.pos + b.neg ≤  b.pos + a.neg) : (intOfRep a ≤ intOfRep b) := h1

theorem exists_intofrep ( a : Int ) : ∃ ( k : IntRep ), a = intOfRep k :=
  by
    refine Quotient.inductionOn a ?_
    intro a
    rw [<-intOfRep]
    exists a

theorem intofrep_lte_trans ( a b c : IntRep ) :
  ((intOfRep a) ≤ (intOfRep b)) → ((intOfRep b) ≤ (intOfRep c)) → ((intOfRep a) ≤ (intOfRep c)) :=
  by
    cases a with
    | mk apos aneg =>
    cases b with
    | mk bpos bneg =>
    cases c with
    | mk cpos cneg =>
    intro h1
    intro h2
    have h3 := intofrep_leq (IntRep.mk bpos bneg) (IntRep.mk cpos cneg) h2
    simp at h3
    have h4 := intofrep_leq (IntRep.mk apos aneg) (IntRep.mk bpos bneg) h1
    simp at h4

    apply intofrep_leq_rev
    simp

    have h5 := MyNat.add_ltes (bpos + cneg) (cpos + bneg) (apos + bneg) (bpos + aneg) h3 h4
    rw (occs := .pos [3]) [MyNat.add_commutes] at h5
    rw (occs := .pos [1]) [MyNat.add_commutes] at h5
    rw [MyNat.add_associates] at h5
    rw (occs := .pos [5]) [MyNat.add_commutes] at h5
    rw [MyNat.add_associates] at h5
    have h6 := MyNat.lte_cancel_left (c := bneg) (apos + (bpos + cneg)) (cpos + (bpos + aneg)) h5
    rw[MyNat.add_commutes] at h6
    rw [MyNat.add_associates] at h6
    rw (occs := .pos [3]) [MyNat.add_commutes] at h6
    rw [MyNat.add_associates] at h6
    have h6 := MyNat.lte_cancel_left (c := bpos) ((cneg + apos)) ((aneg + cpos)) h6
    rw[MyNat.add_commutes] at h6
    rw (occs := .pos [2] )[MyNat.add_commutes] at h6
    exact h6

theorem lte_trans ( a b c : Int) (h1 : a ≤ b ) (h2 : b ≤ c) :
  (a ≤ c) :=
  by
    have h3 := exists_intofrep a
    obtain ⟨x, hx⟩ := h3
    have h4 := exists_intofrep b
    obtain ⟨ y, hy ⟩ := h4
    have h5 := exists_intofrep c
    obtain ⟨ z, hz ⟩ := h5
    rw[hx]
    rw[hz]
    rw[hz] at h2
    rw[hx] at h1
    rw[hy] at h2
    rw[hy] at h1
    exact intofrep_lte_trans x y z h1 h2

theorem lt_means_lte (a b : Int) (h1 : a < b ) : (a ≤ b ) :=
  by
    simp only [(· < · )] at h1
    dsimp [Int.lt] at h1
    exact h1.left

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

theorem zero_leq_one : (Int.zero ≤ Int.one) := rfl
theorem zero_leq_two : (Int.zero ≤ Int.two) := rfl
theorem zero_lt_two : (Int.zero < Int.two) := by
  simp only [(· < · )]
  dsimp [Int.lt]
  constructor
  exact zero_leq_two
  exact two_neq_zero.symm

theorem intofrep_eq_means_leq ( a b : IntRep ) (h1 : a = b) :
  (intOfRep a ≤ intOfRep b) :=
  by
    cases a with
    | mk apos aneg =>
    cases b with
    | mk bpos bneg =>
    simp at h1
    simp only [(· ≤ ·)]
    apply intofrep_leq_rev
    simp
    rw[h1.left]
    rw[h1.right]
    exact MyNat.leq_itself (bpos + bneg)

theorem eq_means_leq ( a b : Int ) (h1 : a = b) :
  (a ≤ b ) :=
  by
    rw[h1]
    refine Quotient.inductionOn b ?_
    intro b
    rw[<-intOfRep]
    exact intofrep_eq_means_leq b b rfl

theorem intofnat_lte_equiv (a b : Nat) (h1 : a ≤ b) :
  (intOfNat a ≤ intOfNat b) :=
  by
    unfold intOfNat
    apply intofrep_leq_rev
    simp
    rw[MyNat.add_zero]
    rw[MyNat.add_zero]
    exact h1

theorem lte_antisym ( a b : Int ) (h1 : Int.lte a b ) (h2 : Int.lte b a) :
  (a = b) :=
  by
    have h3 := exists_intofrep a
    obtain ⟨x, hx⟩ := h3
    have h4 := exists_intofrep b
    obtain ⟨ y, hy ⟩ := h4
    rw[hx] at h1
    rw[hy] at h1
    rw[hx] at h2
    rw[hy] at h2
    have h5 := intofrep_leq x y h1
    have h6 := intofrep_leq y x h2
    cases x with
    | mk xpos xneg =>
    cases y with
    | mk ypos yneg =>
    simp at h5
    simp at h6
    have h7 := MyNat.lte_antisym (xpos + yneg) (ypos + xneg) h5 h6
    rw[hx]
    rw[hy]
    apply intofrep_eq_rev
    simp
    exact h7

theorem int_succ_one (a : Nat) :
  intOfNat (a.succ) = (intOfNat a) + .one :=
  by
    dsimp [Int.one]
    dsimp [intOfNat]
    dsimp [intOfRep]
    apply Quotient.sound
    apply unfold_intrep_equiv_congr
    dsimp [IntRep.Equivalent]
    dsimp [IntRep.add]
    rw[MyNat.add_zero]
    rw[MyNat.add_zero]
    rw[MyNat.add_zero]
    rw[MyNat.add_one]
    rw[MyNat.add_commutes]

theorem negate_lte ( a b : Int ) (h1 : a ≤ b) :
  a.negate ≥ b.negate :=
  by
    have h3 := exists_intofrep a
    obtain ⟨x, hx⟩ := h3
    have h4 := exists_intofrep b
    obtain ⟨ y, hy ⟩ := h4
    cases x with
    | mk xpos xneg =>
    cases y with
    | mk ypos yneg =>
    rw[hx]
    rw[hy]
    simp
    apply intofrep_leq_rev
    dsimp [IntRep.negate]
    rw[hx] at h1
    rw[hy] at h1
    have h5 := intofrep_leq (IntRep.mk xpos xneg) (IntRep.mk ypos yneg) h1
    simp at h5
    rw[MyNat.add_commutes]
    rw (occs := .pos [2]) [MyNat.add_commutes]
    exact h5


theorem int_nat_succ (a : Nat) (b : Int) (h1 : b = intOfNat a) :
  (b + .one = intOfNat (a.succ)) :=
  by
    induction a generalizing b with
    | zero =>
    rw[<-Int.zero] at h1
    rw[h1]
    rw[int_zero_add]
    rfl
    | succ a ih =>
    rw[int_succ_one]
    rw[int_succ_one]
    apply add_right_congr
    apply add_right_cancel (c := Int.one.negate)
    rw[int_add_associates]
    rw[inverse_nat]
    rw[int_add_zero]
    rw[int_succ_one] at h1
    have h2 := add_right_congr b (intOfNat a + Int.one) Int.one.negate h1
    rw[h2]
    rw[int_add_associates]
    rw[inverse_nat]
    rw[int_add_zero]

theorem intrep_apos ( a b c d : Nat) (h1 : (IntRep.mk a b) ≤ (IntRep.mk c d) ) :
  MyNat.Nat.lte (a + d) (c + b) := by exact h1

theorem intofrep_apos (a b c d : Nat ) (h1 : intOfRep (IntRep.mk a b) ≤ intOfRep (IntRep.mk c d)) :
  MyNat.Nat.lte (a  +d ) (c + b) := by exact h1

theorem nonneg_is_nat (a : Int):
  (a ≥ .zero) → (∃ (k : Nat), (a = intOfNat k) ):=
  by
    dsimp [intOfNat]
    refine Quotient.inductionOn a ?_
    intro x
    dsimp [intOfRep]
    intro h1
    cases x with
    | mk apos aneg  =>
    have hpos : (MyNat.Nat.lte aneg apos) := by
      simp only [( · ≥ · )] at h1
      simp only [( · ≤  · )] at h1
      rw[<-intOfRep] at h1
      rw[Int.zero] at h1
      rw[intof_nat_to_rep] at h1
      have hx := intofrep_apos .zero .zero apos aneg h1
      rw[MyNat.zero_add] at hx
      rw[MyNat.add_zero] at hx
      exact hx
    have h2 := MyNat.natural_gap aneg apos hpos
    obtain ⟨ m, hm ⟩ := h2
    exists m
    apply Quotient.sound
    apply unfold_intrep_equiv_congr
    dsimp[IntRep.Equivalent]
    rw[MyNat.add_zero]
    have hm2 := hm.symm
    rw[add_commutes] at hm2
    exact hm2

theorem intofnat_means_geq_zero (a : Int) (b : Nat) (h1: a = intOfNat b) :
  a ≥ .zero := sorry

theorem intofnat_div_means_div ( a b : Nat ) (h1: (intOfNat a).Divides (intOfNat b)) :
  (a.Divides b) := by
    unfold MyNat.Nat.Divides
    unfold Int.Divides at h1
    obtain ⟨ k, hk ⟩ := h1
    have h2 := exists_intofrep k
    obtain ⟨ m, hm ⟩ := h2
    rw[hm] at hk
    unfold intOfNat at hk
    rw[<-mul_mk] at hk
    cases m with
    | mk mpos mneg =>
    simp only [(· * · )] at hk
    dsimp [Mul.mul] at hk
    dsimp [IntRep.mul] at hk
    rw[MyNat.zero_mul] at hk
    rw[MyNat.add_zero] at hk
    rw[MyNat.zero_mul] at hk
    rw[MyNat.add_zero] at hk
    have hk2 := intofrep_eq (IntRep.mk b MyNat.Nat.zero) (IntRep.mk (a*mpos) (a*mneg)) hk
    simp at hk2
    rw[MyNat.zero_add] at hk2
    have hh0 : ((a*mneg) ≤ (a*mpos)) :=
      by
        sorry
    have hh : (mneg ≤ mpos) := by
      sorry
    have hk3 := MyNat.natural_gap (mneg) (mpos) hh
    obtain ⟨r,hr⟩ := hk3
    rw[<-hr] at hk2
    rw[MyNat.add_commutes] at hk2
    exists r
    rw[MyNat.mul_add_distributes] at hk2
    have hr2 := MyNat.add_left_cancel b (a*r) (a*mneg) hk2
    exact hr2

theorem nat_eq_means_intofnat_eq ( a b : Nat ) ( h1 : a = b ) :
  (intOfNat a = intOfNat b) := by
    rw[h1]

theorem prod_geq_means_op_geq (a b : Int) (h1 : .zero ≤ a * b) (h2 : .zero ≤ a) (h3 : a ≠ .zero):
  (.zero ≤ b) :=
  by
    have h3 := nonneg_is_nat a h2
    obtain ⟨ x, hx ⟩ := h3
    have h4 := nonneg_is_nat (a*b) h1
    obtain ⟨ z, hz ⟩ := h4
    rw[hx] at hz
    have h5 : (intOfNat x).Divides (intOfNat z) := by
      unfold Int.Divides
      exists b
      exact hz.symm
    have h6 : (x.Divides z) := intofnat_div_means_div x z h5
    unfold MyNat.Nat.Divides at h6
    obtain ⟨ y, hy ⟩ := h6
    have b_is_nat_y : (b = intOfNat y) := by
      have hh1 := nat_eq_means_intofnat_eq z (x*y) hy
      rw[mul_mk_nat] at hh1
      rw[hh1] at hz
      rw[hx] at h3
      have hh2 := mul_left_divides b (intOfNat y) (intOfNat x) hz h3
      exact hh2
    exact intofnat_means_geq_zero b y b_is_nat_y

theorem not_lt_means_flip_lte ( a b : Int) (h1 : ¬ (a < b)) :
  (b ≤ a) := sorry

theorem not_lte_means_flip_lt ( a b : Int) (h1 : ¬ (a ≤ b)) :
  (b < a) := sorry
theorem geq_zero_means_prod_geq ( a b : Int ) ( h1 : .zero ≤ a ) (h2 : .zero ≤ b) :
  (a ≤ a * b) := sorry

theorem zero_lt_means_one_lte ( a : Int ) (h1: .zero < a) :
  (.one ≤ a) := sorry

theorem geq_one_means_minus_geq_zero (a : Int) (h1 : .one ≤ a) :
  (.zero ≤ (a - .one)) :=
    sorry

theorem prod_nonzero_means_op_nonzero (a b : Int) (h1 : a * b ≠ .zero) :
  (a ≠ .zero) := sorry

theorem zero_lt_means_neq_zero (a : Int) (h1 : .zero < a) :
  (a ≠ .zero) := sorry

theorem lte_less_sum (a b : Int) (h1 : b ≥ .zero) :
  a ≤ a + b := sorry

theorem integer_gaps (a b : Int) (h1 : a ≤ b) :
  ∃ (m : Int), (.zero ≤ m) ∧ (b = a + m) := sorry

theorem lt_means_neq ( a b : Int ) (h1: a < b) : a ≠ b := sorry

theorem sum_lte_is_lte (a b c : Int) (h1: a ≥ c) (h2: b ≥ c) :
  (a + b ≥ c) := sorry

theorem lt_plus_pos_means_lt (a b c: Int) (h1: a ≥ c) (h2 : b > .zero) :
  a + b > c := sorry

theorem lte_add_right (a b c : Int) ( h1 : a ≥ b ) : a + c ≥ b + c :=
  by
    sorry

theorem negative_zero_lte_from_lt ( a : Int) (h1 : a < .zero) :
  (a.negate > .zero) :=
  by
    sorry
end MyInt
