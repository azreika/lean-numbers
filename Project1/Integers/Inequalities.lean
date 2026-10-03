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

theorem zero_lt_one : (Int.zero < Int.one) := by
  simp only [(· < · )]
  dsimp [Int.lt]
  constructor
  rfl

  rw[Int.zero]
  rw[Int.one]
  intro hx
  have hy := intofnat_eq MyNat.Nat.zero MyNat.Nat.one hx
  contradiction

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
  a ≥ .zero :=
  by
    rw[h1]
    rfl

theorem lte_add_rhs (a b : Nat) :
  (a ≤ a + b) :=
  by
    have h1 : (a ≤ a) := MyNat.leq_itself a
    have h2 : (.zero ≤ a) := rfl
    have h3 := MyNat.lte_add_term MyNat.Nat.zero b a h2
    rw[MyNat.zero_add] at h3
    rw[MyNat.add_commutes] at h3
    exact h3

theorem lte_div_left (a b c : Nat) ( h1 : a ≤ b ) :
  (c * a ≤ c * b) :=
  by
    induction c generalizing a b with
    | zero =>
    rw[MyNat.zero_mul]
    rw[MyNat.zero_mul]
    rfl
    | succ c ih =>
    rw[MyNat.add_one]
    rw[MyNat.mul_commutes]
    rw (occs := .pos [2]) [MyNat.mul_commutes]
    rw[MyNat.mul_add_distributes]
    rw[MyNat.mul_add_distributes]
    rw[MyNat.mul_one]
    rw[MyNat.mul_one]
    have h2 := ih a b h1
    have h3 : (a + c * a ≤ a + c * b) :=
      by
        have h4 := MyNat.lte_add_term (c*a) (c*b) a h2
        rw[MyNat.add_commutes]
        rw (occs := .pos [2]) [MyNat.add_commutes]
        exact h4
    have h4 : (c * a ≤ a + c * a) := by
      have h5 := MyNat.lte_add_term .zero a (c*a) rfl
      rw[MyNat.zero_add] at h5
      exact h5
    have h5 : (a + c * a ≤ b + c * a) := MyNat.lte_add_term a b (c*a) h1
    rw[MyNat.mul_commutes]
    rw (occs := .pos [2]) [MyNat.mul_commutes]
    have h5' : (b + c * a ≤ b + c * b) :=
      by
        have h6 := MyNat.lte_add_term (c*a) (c*b) b h2
        rw[MyNat.add_commutes] at h6
        rw (occs := .pos [2]) [MyNat.add_commutes] at h6
        exact h6
    have h6 : (a + c * a ≤ b + c * b) := MyNat.lte_trans (a + c * a) (b + c * a) (b + c * b) h5 h5'
    exact h6

theorem lte_mul_left (a b c : Nat) (h1 : c * a ≤ c * b) (h2 : c ≠ .zero):
  (a ≤ b) :=
  by
    induction a generalizing b c with
    | zero =>
    rfl
    | succ a ih =>
    have h3 := lte_add_rhs a .one
    rw[MyNat.add_commutes] at h3
    rw[<-MyNat.add_one] at h3
    have h4 := lte_div_left a a.succ c h3
    have h5 := MyNat.lte_trans (c*a) (c*a.succ) (c*b) h4 h1
    have ih2 := ih b c h5 h2
    by_cases hx : (a = b)
    rw[hx] at h1
    rw[MyNat.add_one] at h1
    rw[MyNat.mul_add_distributes] at h1
    rw[MyNat.mul_one] at h1
    have h6 := MyNat.add_is_more (c*b) c
    rw[MyNat.add_commutes] at h6
    have h7 := MyNat.lte_antisym (c * b) (c + c*b) h6 h1
    have h8 := MyNat.nat_cancel_to_zero (c*b) c h7
    contradiction

    have hx2 : (a.lt b) := MyNat.lte_and_neq_means_lt a b ih2 hx
    have hx3 := MyNat.lt_means_succ_lte a b hx2
    exact hx3

theorem intofnat_div_means_div ( a b : Nat ) (h1: (intOfNat a).Divides (intOfNat b)) (h2 : a ≠ .zero) :
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
        have hk3 := intofrep_eq (IntRep.mk b MyNat.Nat.zero) (IntRep.mk (a*mpos) (a*mneg)) hk
        have xx1 : (a*mneg ≤ b + a*mneg) := by
          have yy1 : (.zero ≤ b) := rfl
          have yy2 := MyNat.lte_add_term (MyNat.Nat.zero) b (a*mneg) yy1
          rw[MyNat.zero_add] at yy2
          exact yy2
        have xx2 := MyNat.eq_means_leq (b + a *mneg) (a*mpos) hk2
        have xx3 := MyNat.lte_trans (a*mneg ) (b+a*mneg ) (a*mpos) xx1 xx2
        exact xx3
    have hh : (mneg ≤ mpos) := by
      apply lte_mul_left (c:=a)
      exact hh0
      exact h2
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

theorem intof_nat_neq_zero_means_neq (x : Nat) (h1 : intOfNat x ≠ .zero) :
  (x ≠ .zero) :=
  by
    intro x_eq_zero
    have h2 := nat_eq_means_intofnat_eq x .zero x_eq_zero
    rw[<-Int.zero] at h2
    contradiction

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
    have x_neq_zero := h3
    rw[hx] at x_neq_zero
    have x_neq_zero := intof_nat_neq_zero_means_neq x x_neq_zero
    have h6 : (x.Divides z) := intofnat_div_means_div x z h5 x_neq_zero
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


theorem intofnat_lt_equiv (a b : Nat) (h1 : a.lt b) :
  (intOfNat a < intOfNat b) :=
  by
    dsimp [intOfNat]
    simp only [(· < · )]
    dsimp [Int.lt]
    constructor

    apply intofrep_leq_rev
    simp
    rw[MyNat.add_zero, MyNat.add_zero]
    dsimp [MyNat.Nat.lt] at h1
    exact h1.left

    intro h2
    have h3 := intofrep_eq (IntRep.mk a MyNat.Nat.zero) (IntRep.mk b MyNat.Nat.zero) h2
    simp at h3
    rw[MyNat.add_zero, MyNat.zero_add] at h3
    have h4 := MyNat.lt_means_neq a b h1
    contradiction

theorem intofnat_eq_rev (a b : Nat) (h1 : a = b) : intOfNat a = intOfNat b :=
  by
    dsimp [intOfNat]
    apply intofrep_eq_rev
    simp
    rw[MyNat.add_zero, MyNat.add_zero]
    exact h1

theorem intofnat_lt_equiv_rev (a b : Nat) (h1 : intOfNat a < intOfNat b) :
  (a.lt b) :=
  by
    simp only [(· < · )] at h1
    dsimp [Int.lt] at h1
    have h2 := h1.left
    have h3 := h1.right
    dsimp [MyNat.Nat.lt]
    constructor

    dsimp [intOfNat] at h2
    have h4 := intofrep_leq (IntRep.mk a MyNat.Nat.zero) (IntRep.mk b MyNat.Nat.zero) h2
    simp at h4
    rw[MyNat.add_zero, MyNat.add_zero] at h4
    exact h4

    intro h4
    have h5 := intofnat_eq_rev a b h4
    contradiction

theorem intofnat_lte_equiv_rev (a b : Nat) (h1 : intOfNat a ≤ intOfNat b) :
  (a ≤ b) :=
  by
    exact h1

theorem lt_means_neq ( a b : Int ) (h1: a < b) : a ≠ b :=
  by
    simp only [(· < ·)] at h1
    dsimp [Int.lt] at h1
    exact h1.right

theorem contrapositive (a b: Prop) (h1 : a → b) :
  ¬ b → ¬ a :=
  by
    intro h2
    intro ha
    have h3 := h1 ha
    contradiction

theorem eq_means_lte (a b :Int) (h1: a = b) : a ≤ b :=
  by
    rw[h1]
    refine Quotient.inductionOn b ?_
    intro c
    rw[<-intOfRep]
    exact intofrep_eq_means_leq c c rfl

theorem intrep_not_leq_means_not ( a b : IntRep ) (h1 : ¬ (intOfRep a ≤ intOfRep b)) :
  (¬ (a.pos + b.neg ≤  b.pos + a.neg)) :=
  by
    apply Classical.byContradiction
    intro h2
    simp at h2
    have h3 := intofrep_leq_rev a b h2
    contradiction

theorem not_lte_means_flip_lt ( a b : Int) (h1 : ¬ (a ≤ b)) :
  (b < a) :=
  by
    simp only [(· < ·)]
    dsimp [Int.lt]
    constructor

    have h2 := exists_intofrep a
    obtain ⟨ ka , hka ⟩ := h2

    have h3 := exists_intofrep b
    obtain ⟨ kb , hkb ⟩ := h3

    rw[hka]
    rw[hkb]

    apply intofrep_leq_rev
    rw[hka] at h1
    rw[hkb] at h1

    have h2 := intrep_not_leq_means_not ka kb h1
    have h3 := MyNat.not_lte_means_flip_lt (ka.pos + kb.neg) (kb.pos + ka.neg) h2
    have h4 := MyNat.lt_means_lte (kb.pos + ka.neg) (ka.pos + kb.neg) h3
    exact h4

    intro h2
    have h3 := eq_means_lte a b h2.symm
    contradiction

theorem not_lt_means_flip_lte ( a b : Int) (h1 : ¬ (a < b)) :
  (b ≤ a) :=
  by
    simp only [(· < ·)] at h1
    dsimp [Int.lt] at h1
    simp at h1
    by_cases hh: a = b

    have hi := eq_means_leq b a hh.symm
    exact hi

    have h2 := contrapositive (a ≤ b) (a = b) h1 hh
    have h3 := not_lte_means_flip_lt a b h2
    have h4 := lt_means_lte b a h3
    exact h4

theorem geq_zero_means_prod_geq ( a b : Int ) ( h1 : .zero ≤ a ) (h2 : .zero ≤ b) (h3 : b ≠ .zero) :
  (a ≤ a * b) :=
  by
    have h3 := nonneg_is_nat a h1
    have h4 := nonneg_is_nat b h2
    obtain ⟨ aa , ha ⟩ := h3
    obtain ⟨ bb, hb ⟩ := h4

    rw[ha]
    rw[hb]

    rw[<-mul_mk_nat]
    apply intofnat_lte_equiv

    have hbb : (bb ≠ .zero) :=
      by
        intro bx
        have bx' := intofnat_eq_rev bb .zero bx
        rw [<-Int.zero] at bx'
        rw[<-hb] at bx'
        contradiction
    exact MyNat.mul_nonzero_lte aa bb hbb

theorem zero_lt_means_one_lte ( a : Int ) (h1: .zero < a) :
  (.one ≤ a) :=
    by
      simp only [(· < · )] at h1
      dsimp [Int.lt] at h1
      have h2 := h1.left
      have h3 := h1.right
      have h4 := nonneg_is_nat a h2
      obtain ⟨ k, hk ⟩ := h4
      rw[hk]
      rw[hk] at h2
      rw[hk] at h3
      rw[Int.zero] at h3
      rw[Int.zero] at h2

      have h3' : (intOfNat MyNat.Nat.zero ≠ intOfNat k) := h3
      have h4 := intof_nat_neq_zero_means_neq k h3'.symm
      have h5 := MyNat.lte_means_eq_or_one MyNat.Nat.zero k rfl
      have h6 := Or.elim h5 h4.symm
      simp at h6
      rw[<-MyNat.Nat.one] at h6
      rw[Int.one]
      apply intofnat_lte_equiv
      exact h6

theorem zero_lt_means_neq_zero (a : Int) (h1 : .zero < a) :
  (a ≠ .zero) := by
    intro hx
    simp only [(· < · )] at h1
    dsimp [Int.lt] at h1
    have h2 := h1.right
    symm at hx
    contradiction

theorem prod_nonzero_means_op_nonzero (a b : Int) (h1 : a * b ≠ .zero) :
  (a ≠ .zero) :=
  by
    intro h2
    rw[h2] at h1
    rw[int_mul_commutes] at h1
    rw[int_mul_zero] at h1
    contradiction

theorem integer_gaps_pos ( a b : Int ) (h1 : a ≤ b) (a_assumption : a ≥ .zero) :
  ∃ (m : Int), (.zero ≤ m) ∧ (b = a + m) :=
  by
    have a_is_nat := nonneg_is_nat a a_assumption
    obtain ⟨ anat, hanat ⟩ := a_is_nat
    have b_geq_zero := lte_trans .zero a b a_assumption h1
    have b_is_nat := nonneg_is_nat b b_geq_zero
    obtain ⟨ bnat, hbnat ⟩ := b_is_nat

    rw[hbnat] at h1
    rw[hanat] at h1

    have anat_leq_bnat := intofnat_lte_equiv_rev anat bnat h1
    have h_nat_gap := MyNat.natural_gap anat bnat anat_leq_bnat
    obtain ⟨ m, hm ⟩ := h_nat_gap
    exists intOfNat m
    constructor
    rfl

    have hm2 := intofnat_eq_rev (anat + m) bnat hm
    rw[add_mk_nat] at hm2
    rw[<-hanat] at hm2
    rw[<-hbnat] at hm2
    exact hm2.symm

theorem negate_both_sides (a b : Int) (h1 : a = b) :
  a.negate = b.negate :=
  by
    rw[h1]

theorem negate_twice (a : Int) : (a.negate.negate = a) :=
  by
    refine Quotient.inductionOn a ?_
    intro a
    rw[<-intOfRep]
    rw[<-negate_mk]
    rw[<-negate_mk]
    rfl

theorem unfold_lt (a b : Int) (h1 : a < b) : a ≤ b ∧ a ≠ b := by
  exact h1

theorem negative_zero_lte_from_lt ( a : Int) (h1 : a < .zero) :
  (a.negate > .zero) :=
  by
    simp only [(· < · )] at h1
    simp only [(· > · )]
    simp only [(· < · )]
    dsimp [Int.lt] at h1
    dsimp [Int.lt]

    have h2 := h1.left
    have h3 := h1.right
    constructor

    have h4 := exists_intofrep a
    obtain ⟨ k, hk ⟩ := h4
    rw[hk]
    rw[<-negate_mk]
    rw[Int.zero]
    rw[intOfNat]
    apply intofrep_leq_rev
    simp
    rw[MyNat.zero_add, MyNat.add_zero]
    cases k with
    | mk kpos kneg =>
      dsimp [IntRep.negate]
      rw[hk] at h2
      rw[Int.zero, intOfNat] at h2
      have h3 := intofrep_leq (IntRep.mk kpos kneg) (IntRep.mk MyNat.Nat.zero MyNat.Nat.zero) h2
      simp at h3
      rw[MyNat.add_zero, MyNat.zero_add] at h3
      exact h3

    intro h4
    have h5 : Int.zero.negate = a.negate.negate := negate_both_sides Int.zero a.negate h4
    rw[<-zero_negate] at h5
    rw[negate_twice] at h5
    symm at h5
    contradiction

theorem lte_add_right (a b c: Int) (h1 : a ≤ b) : (a + c ≤ b + c) :=
  by
    have h2 := exists_intofrep a
    have h3 := exists_intofrep b
    have h4 := exists_intofrep c

    obtain ⟨ ka, hka ⟩ := h2
    obtain ⟨ kb , hkb ⟩ := h3
    obtain ⟨ kc, hkc ⟩ := h4

    rw[hkc, hkb, hka]
    rw[<-add_mk]
    rw[<-add_mk]
    apply intofrep_leq_rev
    cases ka with
    | mk kapos kaneg =>
    cases kb with
    | mk kbpos kbneg =>
    cases kc with
    | mk kcpos kcneg =>
    simp only [(· + · )]
    dsimp [Add.add]
    dsimp [IntRep.add]
    change (kapos + kcpos + (kbneg + kcneg)) ≤ (kbpos + kcpos) + (kaneg + kcneg)
    rw[<-add_associates]
    rw[<-add_associates]
    apply MyNat.lte_add_term
    rw[MyNat.add_commutes]
    rw (occs := .pos [3]) [MyNat.add_commutes]
    rw[<-add_associates]
    rw[<-add_associates]
    apply MyNat.lte_add_term
    rw[hka] at h1
    rw[hkb] at h1
    have h2 := intofrep_leq (IntRep.mk kapos kaneg) (IntRep.mk kbpos kbneg) h1
    simp at h2
    rw[add_commutes]
    rw (occs := .pos [2]) [add_commutes]
    exact h2

theorem lt_add_right (a b c: Int) (h1 : a < b) : (a + c < b + c) :=
  sorry

theorem integer_gaps (a b : Int) (h1 : a ≤ b) :
  ∃ (m : Int), (.zero ≤ m) ∧ (b = a + m) :=
  by
    exists (b + a.negate)
    constructor
    have h2 := lte_add_right a b a.negate h1
    rw[inverse_nat] at h2
    exact h2

    rw[<-int_add_associates]
    rw[int_add_commutes]
    rw[<-int_add_associates]
    rw[inverse_nat2]
    rw[int_zero_add]


theorem lte_less_sum (a b : Int) (h1 : b ≥ .zero) :
  a ≤ a + b :=
  by
    have h2 := exists_intofrep a
    have h3 := exists_intofrep b

    obtain ⟨ ka, hka ⟩ := h2
    obtain ⟨ kb , hkb ⟩ := h3

    rw[hkb, hka]
    rw[<-add_mk]
    apply intofrep_leq_rev
    cases ka with
    | mk kapos kaneg =>
    cases kb with
    | mk kbpos kbneg =>
    simp only [(· + · )]
    dsimp [Add.add]
    dsimp [IntRep.add]
    change (kapos + (kaneg + kbneg)) ≤  (kapos + kbpos) + kaneg
    rw[add_associates]
    rw[add_commutes]
    rw (occs := .pos [3]) [add_commutes]
    apply MyNat.lte_add_term
    rw[MyNat.add_commutes]
    apply MyNat.lte_add_term
    rw[hkb] at h1
    rw[Int.zero, intOfNat] at h1
    have h5 := intofrep_leq (IntRep.mk MyNat.Nat.zero MyNat.Nat.zero) (IntRep.mk kbpos kbneg) h1
    simp at h5
    rw[MyNat.zero_add, MyNat.add_zero] at h5
    exact h5

theorem lt_plus_pos_means_lt (a b c: Int) (h1: a ≥ c) (h2 : b > .zero) :
  a + b > c :=
  by
    simp only [(· > · )]
    simp only [(· < · )]
    dsimp[Int.lt]
    constructor
    simp only [(· > · )] at h2
    simp only [(· < · )] at h2
    dsimp [Int.lt] at h2
    have h3 := h2.left
    have h4 := h2.right

    have h5 : (a ≤ a + b) :=
      by
        exact lte_less_sum a b h3
    exact lte_trans c a (a + b) h1 h5

    intro hc
    rw[hc] at h1
    have h3 := lte_add_right (a + b) a a.negate h1
    rw[inverse_nat] at h3
    rw[int_add_commutes] at h3
    rw[<-int_add_associates] at h3
    rw[inverse_nat2] at h3
    rw[int_zero_add] at h3
    simp only [(· > · )] at h2
    simp only [(· < · )] at h2
    dsimp [Int.lt] at h2
    have h4 := h2.left
    have h5 := lte_antisym Int.zero b h4 h3
    have h6 := h2.right
    contradiction

theorem geq_one_means_minus_geq_zero (a : Int) (h1 : .one ≤ a) :
  (.zero ≤ (a - .one)) :=
  by
    have h2 := lte_add_right Int.one a Int.one.negate h1
    rw[inverse_nat] at h2
    rw[sub_is_plus_neg]
    exact h2

@[simp] theorem zero_add_nat_simp (a : Nat) : (.zero + a = a) := by
  rw[MyNat.zero_add]

@[simp] theorem add_zero_nat_simp (a : Nat) : (a + .zero = a) := by
  rw[MyNat.add_zero]

@[simp] theorem add_zero_int_simp (a : Int) : (.zero + a = a) := by
  rw[int_zero_add]

@[simp] theorem zero_add_int_simp (a : Int) : (a + .zero = a) := by
  rw[int_add_zero]

@[simp] theorem inverse_nat_simp1 (a : Int) : (a + a.negate = .zero) := by
  rw[inverse_nat]

@[simp] theorem inverse_nat_simp2 (a : Int) : (a.negate + a = .zero) := by
  rw[inverse_nat2]

@[simp] theorem inverse_nat_simp3 (a b : Int) : (b + a) + a.negate = b := by
  rw[int_add_associates]
  simp

@[simp] theorem inverse_nat_simp4 (a b : Int) : (b + a.negate) + a = b := by
  rw[int_add_associates]
  simp

@[simp] theorem int_mul_one_simp (a : Int) : (a * .one = a) := by
  rw[int_mul_one]

@[simp] theorem int_one_mul_simp (a : Int) : (.one * a = a) := by
  rw[int_mul_commutes]
  rw[int_mul_one]

@[simp] theorem int_zero_mul_simp (a : Int) : (.zero * a = .zero) := by
  rw[int_mul_commutes]
  rw[int_mul_zero]

@[simp] theorem int_mul_zero_simp (a : Int) : (a * .zero = .zero) := by
  rw[int_mul_zero]

@[simp] theorem intrep_add_together (a b : IntRep) :
  (a + b) = IntRep.mk (a.pos + b.pos) (a.neg + b.neg) :=
  by
    cases a with
    | mk apos aneg =>
    cases b with
    | mk bpos bneg =>
    simp
    rfl

@[simp] theorem nat_lte_cancel_right1 (a b c d e : Nat) (h1 : a + b + c ≤ d + b + e ) :
  (a + c ≤ d + e ):= by
  rw[add_associates] at h1
  rw[add_associates] at h1
  rw (occs := .pos [2]) [add_commutes] at h1
  rw (occs := .pos [4]) [add_commutes] at h1
  rw[<-add_associates] at h1
  rw[<-add_associates] at h1
  have h2 := MyNat.lte_cancel_right (a + c) (d + e) b h1
  exact h2

@[simp] theorem one_plus_one_is_two : (Int.one + Int.one = Int.two) := by
  rfl

@[simp] theorem two_minus_one_is_one1 : (Int.two + Int.one.negate = Int.one) := by
  apply add_right_cancel (c:=Int.one)
  rw[int_add_associates]
  simp

theorem lte_cancel_right ( a b c : Int ) ( h1 : a + c ≤ b + c ) :
  (a ≤ b ) :=
  by
    have h2 := exists_intofrep a
    have h3 := exists_intofrep b
    have h4 := exists_intofrep c

    obtain ⟨ ka, hka ⟩ := h2
    obtain ⟨ kb , hkb ⟩ := h3
    obtain ⟨ kc, hkc ⟩ := h4

    rw[hka, hkb]
    rw[hka, hkb, hkc] at h1
    rw[<-add_mk] at h1
    rw[<-add_mk] at h1

    have h2 := intofrep_leq (ka + kc) (kb + kc) h1

    apply intofrep_leq_rev
    cases ka with
    | mk kapos kaneg =>
    cases kb with
    | mk kbpos kbneg =>
    cases kc with
    | mk kcpos kcneg =>
    simp
    simp at h2
    rw[<-add_associates] at h2
    rw[<-add_associates] at h2
    have h3 := MyNat.lte_cancel_right (kapos + kcpos + kbneg) (kbpos + kcpos + kaneg) kcneg h2
    rw[add_commutes] at h3
    rw (occs := .pos [3]) [add_commutes] at h3
    rw[<-add_associates] at h3
    rw[<-add_associates] at h3
    have h4 := MyNat.lte_cancel_right (kbneg + kapos) (kaneg + kbpos) kcpos h3
    rw[add_commutes]
    rw (occs := .pos [2]) [add_commutes] at h4
    exact h4

theorem int_lte_mul_left (a b c : Int) (h1 : a ≤ b) (h2: c ≥ .zero) :
  (a * c ≤ b * c) :=
  by
    have h3 := nonneg_is_nat c h2
    obtain ⟨cnat, hcnat ⟩ := h3
    rw[hcnat]

    induction cnat generalizing a b c with
    | zero =>
    rw[<-Int.zero]
    simp
    rfl
    | succ cnat ih =>
    rw[MyNat.add_one]
    rw[add_mk_nat]
    rw[<-Int.one]
    rw[mul_add_distributes]
    rw[mul_add_distributes]
    simp

    by_cases hx : (c = .zero)

    rw[hx] at hcnat
    rw[Int.zero] at hcnat
    have h3 : MyNat.Nat.zero = cnat.succ :=
        intofnat_eq MyNat.Nat.zero cnat.succ hcnat
    contradiction

    have c_geq_one : (c ≥ .one ) := by
      rw[hcnat]
      rw[Int.one]
      apply intofnat_lte_equiv
      rw[hcnat] at h2
      rw[Int.zero] at h2
      have h3 := intofnat_lte_equiv_rev MyNat.Nat.zero cnat h2
      have h4 := MyNat.lte_add_term MyNat.Nat.zero cnat MyNat.Nat.one h3
      simp at h4
      rw[<-MyNat.succ_add_one] at h4
      exact h4

    have c_one_geq_zero : (c - .one ≥ .zero) := by
      rw[sub_is_plus_neg]
      have hx2 : ((c + Int.one.negate) + Int.one ≥ Int.zero + Int.one) := by
        rw[int_add_associates]
        simp
        exact c_geq_one
      exact lte_cancel_right (Int.zero) (c + Int.one.negate)  (Int.one) hx2

    have csucc_geq2 : (c - .one = intOfNat cnat) := by
      apply add_right_cancel (c := Int.one)
      rw[sub_is_plus_neg]
      rw[int_add_associates]
      simp
      rw[Int.one]
      rw[<-add_mk_nat]
      rw[<-MyNat.succ_add_one]
      exact hcnat
    have tt1 : (a * (intOfNat cnat) ≤ b * (intOfNat cnat)) := by
      have ih2 := ih a b (c - .one) h1 c_one_geq_zero csucc_geq2
      exact ih2
    have tt2 : (a + a * (intOfNat cnat) ≤ b + a * (intOfNat cnat)) := by
      have h3 := lte_add_right a b (a * intOfNat cnat) h1
      exact h3
    have tt3 : (b + a * (intOfNat cnat) ≤ b + b * (intOfNat cnat)) := by
      have h3 := lte_add_right (a * intOfNat cnat) (b * intOfNat cnat) b tt1
      rw[int_add_commutes]
      rw (occs := .pos [2]) [int_add_commutes]
      exact h3
    exact lte_trans (a + a * (intOfNat cnat)) (b + a * (intOfNat cnat)) (b + b * (intOfNat cnat)) tt2 tt3

end MyInt
