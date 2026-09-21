import Project1.Integers.Integers
import Project1.Nat.Properties

import Std

namespace MyInt
open Classical

abbrev mul_associates := MyNat.mul_associates

theorem int_rep_add_associates ( a b c : IntRep ) :
  (a + b) + c = a + (b + c ) := by
    cases a with
    | mk apos aneg =>
      cases b with
      | mk bpos bneg =>
        cases c with
        | mk cpos cneg =>
          change (IntRep.mk (apos + bpos + cpos) (aneg + bneg + cneg)) =
                  (IntRep.mk (apos + (bpos + cpos)) (aneg + (bneg + cneg)))
          rw[MyNat.add_associates]
          rw[MyNat.add_associates]

theorem int_add_associates (a b c : Int ) :
  (a + b) + c = a + (b + c ) :=
  by
    refine Quotient.inductionOn₃ a b c ?_
    intro x y z
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-add_mk]
    rw[<-add_mk]
    rw[<-add_mk]
    rw[<-add_mk]
    rw[int_rep_add_associates]

theorem int_add_zero (a : Int) :
  a + .zero = a :=
  by
    refine Quotient.inductionOn a ?_
    intro x
    rw[<-intOfRep]
    unfold Int.zero
    rw[intof_nat_to_rep]
    rw[<-add_mk]
    cases x with
    | mk pos neg =>
      dsimp[Int]
      apply Quotient.sound
      change (IntRep.mk pos neg ) + (IntRep.mk .zero .zero) ≈ (IntRep.mk pos neg)
      change (IntRep.mk (pos + .zero) (neg + .zero) ) ≈ (IntRep.mk pos neg)
      rw[MyNat.add_zero]
      rw[MyNat.add_zero]
      exact equi_refl (IntRep.mk pos neg)

theorem intrep_add_left_congr ( a b c : IntRep ) ( h1 : a = b ) :
  (c + a = c + b) :=
  by
    rw[h1]


theorem intrep_add_right_congr ( a b c : IntRep ) ( h1 : a = b ) :
  (a + c = b + c) :=
  by
    rw[h1]

theorem add_left_congr ( a b c : Int ) ( h1 : a = b ) :
  (c + a = c + b) :=
  by
    rw[h1]

theorem add_right_congr ( a b c : Int ) ( h1 : a = b ) :
(a + c = b + c) :=
  by
    rw[h1]

theorem intrep_add_commutes ( a b : IntRep ) : a + b = b + a :=
  by
    simp only [(· + ·)]
    dsimp [Add.add]
    dsimp [IntRep.add]
    rw[add_commutes]
    rw (occs := .pos [2] ) [add_commutes]

theorem intrep_mul_associates (a b c : IntRep ) :
  (a * b) * c = a * (b * c) :=
  by
    cases a with
    | mk apos aneg =>
      cases b with
      | mk bpos bneg =>
        cases c with
        | mk cpos cneg =>
          simp only [(· * ·)]
          unfold Mul.mul
          unfold instMulIntRep
          simp
          dsimp [IntRep.mul]
          simp

          rw[mul_commutes]
          rw[MyNat.mul_add_distributes]
          rw[MyNat.mul_add_distributes]
          rw[mul_commutes]
          rw[mul_associates]
          rw[add_associates]
          rw[add_associates]

          constructor

          apply MyNat.add_left_congr
          rw[MyNat.mul_add_distributes]
          rw[<-add_associates]
          rw (occs := .pos [3]) [add_commutes]
          rw[mul_commutes]
          rw[mul_associates]
          apply MyNat.add_left_congr
          rw[mul_commutes]
          rw[MyNat.mul_add_distributes]
          rw[mul_commutes]
          rw[mul_associates]
          apply MyNat.add_left_congr
          rw[mul_commutes]
          rw[mul_associates]

          rw[mul_commutes]
          rw[MyNat.mul_add_distributes]
          rw[MyNat.mul_add_distributes]
          rw[mul_commutes]
          rw[mul_associates]
          rw[add_associates]
          rw[add_associates]
          apply MyNat.add_left_congr
          rw[MyNat.mul_add_distributes]
          rw[<-add_associates]
          rw (occs := .pos [3]) [add_commutes]
          rw[mul_commutes]
          rw[mul_associates]
          apply MyNat.add_left_congr
          rw[mul_commutes]
          rw[MyNat.mul_add_distributes]
          rw[mul_commutes]
          rw[mul_associates]
          apply MyNat.add_left_congr
          rw[mul_commutes]
          rw[mul_associates]

theorem int_mul_associates (a b c : Int ) :
  (a * b) * c = a * (b * c ) :=
  by
    refine Quotient.inductionOn₃ a b c ?_
    intro x y z
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-mul_mk]
    rw[<-mul_mk]
    rw[<-mul_mk]
    rw[<-mul_mk]
    rw[intrep_mul_associates]

theorem int_mul_commutes ( a b : Int ) :
  a * b = b * a :=
  by
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-mul_mk]
    rw[<-mul_mk]
    rw[intrep_mul_commutes]

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
  .zero + a = a :=
  by
    rw[int_add_commutes]
    rw[int_add_zero]

theorem left_divides ( p m : Int ) :
  (p.Divides (p*m)) :=
  by
    unfold Int.Divides
    exists m

theorem intrep_expand_negate (a b : IntRep) : a * (b.negate) = (a * b).negate :=
  by
    rw[mul_expands]
    rw[mul_expands]
    cases a with
    | mk apos aneg =>
      cases b with
      | mk bpos bneg =>
        dsimp [IntRep.negate]
        dsimp [IntRep.mul]

theorem int_expand_negate ( a b : Int ) :
  a * (b.negate) = (a * b).negate :=
  by
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-negate_mk]
    rw[<-mul_mk]
    rw[<-mul_mk]
    rw[<-negate_mk]
    rw[intrep_expand_negate]

theorem add_negate ( a b : Int ) (h1: a = b) : a.negate = b.negate := by rw[h1]

theorem double_negate ( a : Int ) : a.negate.negate = a :=
  by
    refine Quotient.inductionOn a ?_
    intro a
    rw[<-intOfRep]
    rw[<-negate_mk]
    rw[<-negate_mk]
    unfold IntRep.negate
    simp

theorem drop_negate ( a b : Int ) (h1: a.negate = b.negate ) :
  a = b :=
  by
    have h2 := add_negate a.negate b.negate h1
    rw[double_negate] at h2
    rw[double_negate] at h2
    exact h2

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

theorem even_squared_is_even (n : Int) (h1: Int.Even n) : (Int.Even (n * n)) :=
  by
    unfold Int.Even
    unfold Int.Even at h1
    unfold Int.Divides at h1
    obtain ⟨ k , hk ⟩ := h1
    rw[hk]
    rw[int_mul_associates]
    unfold Int.Divides
    exists (k * (.two * k))

theorem intrep_mul_def (a b : IntRep ) :
  a * b = (IntRep.mk (a.pos * b.pos + a.neg * b.neg) (a.pos * b.neg + a.neg * b.pos)) :=
  by rfl

theorem pos_expands (a b : IntRep) :
  (a + b).pos = a.pos + b.pos := by rfl

theorem neg_expands (a b : IntRep) :
  (a + b).neg = a.neg + b.neg := by rfl

theorem intrep_mul_add_distributes ( a b c : IntRep) :
  a * (b + c) = a * b + a * c :=
  by
    rw[mul_expands]
    rw[mul_expands]
    rw[mul_expands]
    cases a with
    | mk apos aneg =>
      dsimp [IntRep.mul]
      rw[add_combines]
      rw[pos_expands]
      rw[neg_expands]
      rw[MyNat.mul_add_distributes]
      rw[MyNat.mul_add_distributes]
      rw[MyNat.mul_add_distributes]
      rw[MyNat.mul_add_distributes]
      cases b with
      | mk bpos bneg =>
        dsimp [IntRep.mul]
        rw[add_combines]
        cases c with
        | mk cpos cneg =>
          dsimp [IntRep.mul]
          rw[add_combines]
          rw[add_combines]
          rw[add_combines]
          rw[int_rep_add_associates]
          rw[int_rep_add_associates]
          apply intrep_add_left_congr
          rw[<-int_rep_add_associates]
          rw[<-int_rep_add_associates]
          apply intrep_add_right_congr
          rw[intrep_add_commutes]

theorem mul_add_distributes ( a b c : Int ) :
  a * (b + c) = a * b + a * c :=
  by
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-intOfRep]
    rw[<-mul_mk]
    rw[<-mul_mk]
    rw[<-add_mk]
    rw[<-add_mk]
    rw[<-mul_mk]
    rw[intrep_mul_add_distributes]

theorem divides_sum ( p a b : Int ) (h1: p.Divides a) (h2 : p.Divides b) :
  (p.Divides (a + b)) :=
  by
    dsimp [Int.Divides] at h1
    dsimp [Int.Divides] at h2
    obtain ⟨ k, hk ⟩ := h1
    obtain ⟨ m, hm ⟩ := h2
    dsimp [Int.Divides]
    exists ( m + k )
    rw [mul_add_distributes]
    rw[hk]
    rw[hm]
    rw[int_add_commutes]

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
    have h2 := add_right_congr (p*k + b) (p*m) (p*k).negate hm
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

theorem mul_left_congr ( a b c : Int ) ( h1 : a = b ) : (c * a = c * b) := by rw[h1]

theorem intrep_add (a b: IntRep) : (a + b = a.add b) := rfl

theorem intrep_additive_inverse (a : IntRep ) : (a + a.negate ≈ IntRep.zero ) :=
  by
    cases a with
    | mk pos neg =>
      dsimp [IntRep.negate]
      apply unfold_intrep_equiv_congr
      dsimp [IntRep.Equivalent]
      rw[IntRep.zero]
      rw[MyNat.add_zero]
      rw[MyNat.zero_add]
      rw[pos_expands]
      rw[neg_expands]
      dsimp [IntRep.neg]
      rw[add_commutes]

theorem additive_inverse ( a : Int) : (a + a.negate = .zero) :=
  by
    refine Quotient.inductionOn a ?_
    intro a
    apply Quotient.sound
    rw [<-intrep_add]
    have h2 := intrep_additive_inverse a
    exact h2

theorem neg_expands_mul ( a b : Int ) : (a * b).negate = a * (b.negate) :=
  by
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    apply Quotient.sound
    dsimp[IntRep.negate]
    apply unfold_intrep_equiv_congr
    dsimp[IntRep.Equivalent]
    dsimp[IntRep.mul]

theorem zero_or_nonzero (a : Int) : (a = .zero ∨ a ≠ .zero) := by
  apply Classical.em

theorem intrep_zero_pos : IntRep.zero.pos = .zero := rfl
theorem intrep_zero_neg : IntRep.zero.neg = .zero := rfl
theorem intrep_zero_negate : IntRep.zero.negate = IntRep.zero := rfl

theorem dn ( p : Prop) : ¬¬p -> p := by simp

theorem intrep_eq_negate (a b : IntRep) (h1 : a ≈ b) :
  (a.negate ≈ b.negate) := sorry

theorem intrep_mul_to_zero ( a b : IntRep ) (h1 : a * b ≈ .zero) :
  (a ≈ .zero ∨ b ≈ .zero):=
  by
    have h0 : (a ≈ .zero ∨ ¬ (a ≈ .zero)) := Classical.em (a ≈ .zero)
    cases h0 with
    | inl hh =>
    left
    exact hh
    | inr hh =>
    right

    have h2 := unfold_intrep_equiv (a*b) .zero h1

    unfold IntRep.Equivalent at h2
    rw[intrep_zero_neg] at h2
    rw[MyNat.add_zero] at h2
    rw[intrep_zero_pos] at h2
    rw[MyNat.zero_add] at h2


    apply unfold_intrep_equiv_congr
    dsimp [IntRep.Equivalent]
    rw[intrep_zero_neg]
    rw[MyNat.add_zero]
    rw[intrep_zero_pos]
    rw[MyNat.zero_add]



    cases a with
    | mk apos aneg =>
    cases b with
    | mk bpos bneg =>
    rw[mul_expands] at h2
    dsimp [IntRep.mul] at h2
    dsimp [IntRep.pos]

    induction bpos generalizing apos aneg bneg with
    | zero =>
    rw[MyNat.mul_zero, MyNat.mul_zero, MyNat.zero_add, MyNat.add_zero] at h2
    apply dn
    intro h0

    have h0' : (bneg ≠ MyNat.Nat.zero) := by
      symm
      simp
      exact h0
    have h3 : (aneg = apos) := MyNat.div_cancels aneg apos bneg h0' h2
    have h4 := inteq_means_zero (IntRep.mk apos aneg)
    symm at h3
    rw[h4] at h3
    contradiction

    | succ bpos ih =>
    have htan := ih apos aneg hh
    cases bpos with
      | zero =>
      rw[<-MyNat.Nat.one, MyNat.mul_one, MyNat.mul_one] at h2
      cases bneg with
        | zero => contradiction
        | succ bneg =>
        rw[MyNat.succ_same]
        have h3 := htan bneg
        rw[mul_expands] at h3
        dsimp[IntRep.mul] at h3
        rw[MyNat.mul_zero] at h3
        rw[MyNat.zero_add] at h3
        rw[MyNat.mul_zero] at h3
        rw[MyNat.add_zero] at h3

        rw[MyNat.add_one, MyNat.mul_add_distributes, MyNat.mul_one, MyNat.mul_add_distributes] at h2
        rw[MyNat.mul_one, MyNat.add_associates] at h2
        have h2 := MyNat.add_left_cancel (aneg + aneg * bneg) (apos * bneg + aneg) apos h2

        simp only [(· ≈ ·)] at h3
        dsimp [instHasEquivOfSetoid, Setoid.r, IntRep.Equivalent] at h3
        rw[intrep_zero_pos] at h3
        rw[MyNat.zero_add] at h3
        rw[intrep_zero_neg] at h3
        rw[MyNat.add_zero] at h3
        rw[MyNat.add_commutes] at h2
        have h2 := MyNat.add_right_cancel (aneg * bneg) (apos * bneg) aneg h2
        have h3 := h3 h2 h2
        exact h3
      | succ bpos =>
      cases bneg with
      | zero =>
      rw[MyNat.mul_zero] at h2
      rw[MyNat.mul_zero] at h2
      rw[MyNat.add_zero] at h2
      rw[MyNat.zero_add] at h2
      have h0 : (bpos.succ.succ ≠ .zero) := MyNat.succed_is_nonzero bpos.succ
      have h3 : (apos = aneg) := MyNat.div_cancels apos aneg (bpos.succ.succ) h0 h2
      have h4 := inteq_means_zero (IntRep.mk apos aneg)
      rw[h4] at h3
      contradiction
      | succ bneg =>
      rw[MyNat.succ_same]
      have h3 := htan bneg
      rw[mul_expands] at h3
      dsimp[IntRep.mul] at h3

      rw[MyNat.add_one] at h2
      rw[MyNat.mul_add_distributes, MyNat.mul_one] at h2
      rw[MyNat.mul_add_distributes, MyNat.mul_one] at h2
      rw[MyNat.add_associates] at h2
      rw[MyNat.add_one] at h2
      rw[MyNat.add_one] at h2
      rw[MyNat.mul_add_distributes, MyNat.mul_one] at h2
      rw[MyNat.mul_add_distributes, MyNat.mul_one] at h2
      rw[MyNat.mul_add_distributes] at h2
      rw[MyNat.mul_add_distributes] at h2
      rw[MyNat.mul_one] at h2
      rw[MyNat.mul_one] at h2
      rw[MyNat.add_associates] at h2
      rw[MyNat.add_associates] at h2

      have h2 := MyNat.add_left_cancel (apos + (apos * bpos + (aneg + aneg * bneg))) (apos * bneg + (aneg + (aneg + aneg * bpos))) apos h2

      simp only [(· ≈ ·)] at h3
      dsimp [instHasEquivOfSetoid, Setoid.r, IntRep.Equivalent] at h3
      rw[intrep_zero_pos] at h3
      rw[MyNat.zero_add] at h3
      rw[intrep_zero_neg] at h3
      rw[MyNat.add_zero] at h3
      rw[MyNat.add_one] at h3

      rw[MyNat.mul_add_distributes] at h3
      rw[MyNat.mul_add_distributes] at h3
      rw[MyNat.mul_one] at h3
      rw[<-MyNat.add_associates] at h2
      rw[<-MyNat.add_associates] at h2
      rw[<-MyNat.add_associates] at h2
      rw[<-MyNat.add_associates] at h2
      rw (occs := .pos [2]) [MyNat.add_commutes] at h2
      rw (occs := .pos [5]) [MyNat.add_commutes] at h2
      rw[MyNat.add_associates] at h2
      rw[MyNat.add_associates] at h2
      rw[MyNat.add_associates] at h2
      have h2 := MyNat.add_left_cancel (apos + (apos * bpos + aneg * bneg)) (apos * bneg + aneg +aneg*bpos) aneg h2
      rw[MyNat.add_associates] at h3
      rw[MyNat.add_associates] at h2
      have h4 := h3 h2 h2
      rw[add_commutes] at h4
      rw[<-MyNat.succ_add_one] at h4
      exact h4

theorem mul_to_zero ( a b : Int ) (h1 : a * b = .zero) :
  (a = .zero ∨ b = .zero) :=
  by
    sorry

theorem mul_left_divides( a b c : Int ) ( h1 : c * a = c * b ) (hc : c ≠ .zero) :
  (a = b) :=
  by
    have h2 := add_left_congr (c*a) (c*b) (c * b).negate h1
    rw[int_add_commutes] at h2
    rw (occs := .pos [2]) [int_add_commutes] at h2
    rw[additive_inverse] at h2
    rw[neg_expands_mul] at h2
    rw[<-mul_add_distributes] at h2
    have h3 : (c = .zero ∨ (a + b.negate = .zero)) := mul_to_zero c (a + b.negate) h2
    sorry

theorem intofnat_mul (a b : Nat) :
  (intOfNat a) * (intOfNat b) = intOfNat (a * b) :=
  by
    rw[intof_nat_to_rep]
    simp only [(· * ·)]
    apply Quotient.sound
    unfold instHasEquivOfSetoid intRepSetoid IntRep.Equivalent
    simp
    rw[MyNat.add_zero]
    unfold MyNat.instMulNat
    dsimp [IntRep.mul]
    rw[MyNat.zero_mul]
    rw[MyNat.add_zero]
    rw[MyNat.zero_mul]
    rw[MyNat.add_zero]
    rw[MyNat.mul_zero]
    rfl

theorem intofnat_add (a b : Nat) :
  (intOfNat a) + (intOfNat b) = intOfNat (a + b) :=
  by
    unfold intOfNat
    rfl

theorem two_squared : (.two * .two = Int.four) := by
  unfold Int.two
  unfold Int.four
  rw[intofnat_mul]
  rfl

theorem one_plus_one : (Int.one + .one = .two) := by
  unfold Int.one
  unfold Int.two
  rfl

theorem int_mul_one ( a : Int ) : a * .one = a := by
    refine Quotient.inductionOn a ?_
    intro a
    rw[<-intOfRep]
    rw[Int.one]
    rw[intof_nat_to_rep]
    rw[<-mul_mk]
    apply Quotient.sound
    cases a with
    | mk pos neg =>
      simp only [(· * · )]

      unfold Mul.mul instMulIntRep
      simp

      unfold IntRep.mul
      simp

      unfold instHasEquivOfSetoid intRepSetoid IntRep.Equivalent
      dsimp[IntRep.Equivalent]

      rw[MyNat.mul_one]
      rw[MyNat.mul_zero]
      rw[MyNat.add_zero]
      rw[MyNat.mul_zero]
      rw[MyNat.mul_one]
      rw[MyNat.zero_add]

theorem add_self (a : Int) : (a + a = .two * a):= by
  rw[<-int_mul_one a]
  rw[<-mul_add_distributes]
  rw[one_plus_one]
  rw[int_mul_one]
  rw[int_mul_commutes]

theorem rearrange_22k (k : Int ) :
  (.two * (.two * k)) = (.four * k) :=
  by
    rw[<-int_mul_associates]
    rw[two_squared]

theorem rearrange_22k_2 ( k : Int ) :
  (.two * k + .two * k) = (.four * k) := by
    rw[<-mul_add_distributes]
    rw[add_self]
    rw[<-int_mul_associates]
    rw[two_squared]

theorem odd_squared_is_odd (n : Int) (h1 : Int.Odd n) : (Int.Odd (n * n)) :=
  by
    unfold Int.Odd
    unfold Int.Odd at h1
    obtain ⟨ k, hk ⟩ := h1
    rw[hk]
    exists (.two*k*k + .two * k)
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

theorem one_is_unit (a : Int) (h1: a.Divides .one) : a = .one :=
  by sorry

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

theorem even_is_mult_of_two (a : Int) (h1 : Int.Even a) : (∃ (k : Int), a = .two * k) :=
  by
    unfold Int.Even at h1
    unfold Int.Divides at h1
    exact h1

theorem common_div_divides_gcd ( a b d : Int )
  (h1:  d.Divides a)
  (h2 : d.Divides b) :
  (d.Divides (Int.gcd a b)) := sorry

theorem even_means_two_divides (a : Int ) (h1 : Int.Even a) : Int.two.Divides a :=
  by
    unfold Int.Even at h1
    exact h1

theorem intofrep_eq ( a b : IntRep ) (h1 : intOfRep a = intOfRep b) :
  (a.pos + b.neg = a.neg + b.pos) :=
  by
    cases a with
    | mk apos aneg =>
      cases b with
      | mk bpos bneg =>
        simp
        sorry

theorem intrep_onlypos (a b : IntRep) (heq : a = b) (ha: a.neg = .zero) (hb: b.neg = .zero) :
  (a.pos = b.pos) := sorry

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
    have h10 : (Int.two = Int.one) := one_is_unit .two h9
    have h12 := And.intro h10 int_two_neq_one
    simp at h12

end MyInt
