import Project1.Nat.Nat
import Project1.Nat.Arithmetic
import Project1.Nat.Properties

import Project1.IntReps.IntRep

namespace MyInt

def Int := Quotient intRepSetoid

def intOfRep ( r : IntRep ) : Int := Quotient.mk intRepSetoid r

def intOfNat ( n : Nat ) : Int := intOfRep (IntRep.mk n .zero )

theorem anegneg_is_apos (a : IntRep) :
  a.negate.neg = a.pos := by rfl

theorem anegpos_is_aneg ( a : IntRep) :
  a.negate.pos = a.neg := by rfl

theorem negate_respects ( a b : IntRep ) ( h : a.Equivalent b ) :
  (a.negate.Equivalent b.negate) :=
  by
    unfold IntRep.Equivalent
    unfold IntRep.Equivalent at h
    rw[anegneg_is_apos]
    rw[anegneg_is_apos]
    rw[anegpos_is_aneg]
    rw[anegpos_is_aneg]
    rw[add_commutes]
    apply Eq.symm
    rw[add_commutes]
    exact h

def Int.negate : Int -> Int :=
  Quotient.lift
    (fun x => Quotient.mk intRepSetoid (IntRep.negate x))
    (by
      intro a b h
      apply Quotient.sound
      exact negate_respects a b h
    )

theorem add_respects (a a' b b' : IntRep ) (ha: a ≈ a') (hb: b ≈ b') :
  IntRep.add a b ≈ IntRep.add a' b' :=
  by
    simp only [(· ≈ · )]
    unfold instHasEquivOfSetoid
    simp
    simp[Setoid.r]
    unfold IntRep.Equivalent
    dsimp [IntRep.add]

    have ha2 := unfold_intrep_equiv a a' ha
    have ha3 := unfold_intrep_equiv b b' hb

    unfold IntRep.Equivalent at ha2
    unfold IntRep.Equivalent at ha3
    rw[add_associates]
    rw (occs := .pos [2]) [add_commutes]
    rw[<-add_associates]
    rw[<-add_associates]
    rw[ha2]
    rw[add_associates]
    rw[add_associates]
    rw[add_associates]
    apply MyNat.add_left_congr
    rw (occs := .pos [2]) [<-add_associates]
    rw (occs := .pos [4]) [add_commutes]
    rw[add_associates]
    apply MyNat.add_left_congr
    rw[add_commutes]
    exact ha3

instance : Add IntRep where
  add := IntRep.add

instance : Mul IntRep where
  mul := IntRep.mul

theorem intrep_mul_commutes (a b : IntRep ) :
  (a * b = b * a) :=
  by
    simp [(· * · )]
    dsimp [Mul.mul]
    dsimp [IntRep.mul]
    simp

    constructor
    rw[MyNat.mul_commutes]
    apply MyNat.add_left_congr
    rw[MyNat.mul_commutes]

    rw[MyNat.mul_commutes]
    rw (occs := .pos [2]) [add_commutes]
    apply MyNat.add_left_congr
    rw[MyNat.mul_commutes]

theorem add_combines (xpos ypos xneg yneg : Nat) :
  (IntRep.mk (xpos + ypos) (xneg + yneg)) = ((IntRep.mk xpos xneg) + (IntRep.mk ypos yneg)) :=
  by
    rfl

theorem posneg_preserves_lt ( a b : IntRep ) (h1 : a ≈ b ) (h2: (MyNat.Nat.lte a.neg a.pos) ) :
  (MyNat.Nat.lte b.neg b.pos) :=
  by
    have h3 := unfold_intrep_equiv a b h1
    unfold IntRep.Equivalent at h3
    cases a with
    | mk posa nega =>
      simp at h2
      simp at h3
      cases b with
      | mk posb negb =>
        simp at h3
        simp
        rw[add_commutes] at h3
        have h4 : (MyNat.Nat.lte (negb + nega) (negb + posa)) := by
          rw[add_commutes]
          rw (occs := .pos [2]) [add_commutes]
          apply MyNat.lte_add_term
          exact h2
        rw[h3] at h4
        have h5 : (MyNat.Nat.lte negb posb) := MyNat.lte_cancel_right negb posb nega h4
        exact h5

theorem mul_extracts (a xpos xneg : Nat) :
  (IntRep.mk (a * xpos) (a*xneg)) = ((IntRep.mk a .zero) * (IntRep.mk xpos xneg)) :=
  by
    simp only [(· * · )]
    dsimp [Mul.mul]
    unfold IntRep.mul
    simp
    rw[MyNat.zero_mul]
    rw[MyNat.zero_mul]
    rw[MyNat.add_zero]
    rw[MyNat.add_zero]
    constructor
    rfl
    rfl

theorem mul_respects_left (a a' b : IntRep) (h1: a ≈ a') :
  a * b ≈ a' * b :=
  by
    apply unfold_intrep_equiv_congr
    unfold IntRep.Equivalent
    simp [(· * ·)]
    unfold Mul.mul
    unfold instMulIntRep
    simp
    dsimp [IntRep.mul]
    have h3 := unfold_intrep_equiv a a' h1
    dsimp [IntRep.Equivalent] at h3
    have h4 := MyNat.mul_left (a.pos + a'.neg) (a'.pos + a.neg) b.pos h3
    rw[MyNat.mul_add_distributes] at h4
    rw[MyNat.mul_add_distributes] at h4
    rw[MyNat.mul_commutes] at h4
    rw (occs := .pos [3] ) [add_commutes]
    rw (occs := .pos [3] ) [MyNat.mul_commutes]
    rw[add_associates]
    rw (occs := .pos [2] ) [add_commutes]
    rw[<-add_associates]
    rw[<-add_associates]
    rw[h4]
    rw[MyNat.mul_commutes]
    rw[add_associates]
    rw[add_associates]
    rw[add_associates]
    apply MyNat.add_left_congr
    rw[MyNat.mul_commutes]
    rw (occs := .pos [2]) [<-add_associates]
    rw (occs := .pos [3]) [add_commutes]
    apply MyNat.add_left_congr
    have h5 := (MyNat.mul_left (a.pos + a'.neg) (a'.pos + a.neg) b.neg h3).symm
    rw[MyNat.mul_add_distributes] at h5
    rw[MyNat.mul_add_distributes] at h5
    rw[MyNat.mul_commutes] at h5
    rw (occs := .pos [2]) [MyNat.mul_commutes]
    rw[h5]
    rw[MyNat.mul_commutes]
    rw[add_commutes]
    apply MyNat.add_right_congr
    rw[MyNat.mul_commutes]

theorem mul_respects_right (a a' b : IntRep) (h1: a ≈ a') :
  b * a ≈ b * a' :=
  by
    rw[intrep_mul_commutes]
    rw (occs := .pos [2]) [intrep_mul_commutes]
    have h2 := mul_respects_left a a' b h1
    exact h2

theorem mul_respects (a a' b b' : IntRep ) (ha: a ≈ a') (hb: b ≈ b') :
  IntRep.mul a b ≈ IntRep.mul a' b' :=
  by
    have h1 : a.mul b ≈ a'.mul b := mul_respects_left a a' b ha
    have h2 : a'.mul b ≈ a'.mul b' := mul_respects_right b b' a' hb
    have h3 := equi_trans (a.mul b) (a'.mul b) (a'.mul b') h1 h2
    exact h3

def Int.add : Int -> Int -> Int :=
  Quotient.lift
  ( fun x => Quotient.lift
      ( fun y => Quotient.mk intRepSetoid (IntRep.add x y))
      (by
        intro a b h
        apply Quotient.sound
        have h0 := equi_refl x
        rw [<-IntRep.equiv_def] at h0
        have h2 := add_respects x x a b h0 h
        exact h2
      )
  )
  (
    by
      intro a b h
      funext y

      refine Quotient.inductionOn y ?_
      intro c

      have h0 := equi_refl c
      rw [<-IntRep.equiv_def] at h0


      apply Quotient.sound
      have h1 := add_respects a b c c h h0
      exact h1
  )

def Int.mul : Int -> Int -> Int :=
  Quotient.lift
   ( fun x => Quotient.lift
      ( fun y => Quotient.mk intRepSetoid (IntRep.mul x y))
      (by
        intro a b h
        apply Quotient.sound
        have h0 := equi_refl x
        rw [<-IntRep.equiv_def] at h0
        have h2 := mul_respects x x a b h0 h
        exact h2
      )
  )
  (
    by
      intro a b h
      funext y

      refine Quotient.inductionOn y ?_
      intro c

      have h0 := equi_refl c
      rw [<-IntRep.equiv_def] at h0

      apply Quotient.sound
      have h1 := mul_respects a b c c h h0
      exact h1
  )

def IntRep.zero := IntRep.mk .zero .zero
def zero_int_rep := IntRep.zero

def Int.zero := intOfNat .zero
def Int.one := intOfNat .one
def Int.two := intOfNat .two
def Int.three := intOfNat .three
def Int.four := intOfNat .four

theorem intof_nat_to_rep (x : Nat) :
  (intOfNat x) = (intOfRep (IntRep.mk x .zero)) := rfl

theorem negate_mk ( x : IntRep ) :
  intOfRep (x.negate) = (Int.negate (intOfRep x)):=
  by
    unfold intOfRep
    apply Quotient.sound
    unfold IntRep.negate
    rfl


instance : Add Int where
  add := Int.add

instance : Mul Int where
  mul := Int.mul

def Int.subtract (a b : Int): Int :=
  a + b.negate

instance : Sub Int where
  sub := Int.subtract

theorem add_mk ( x y : IntRep ) :
  intOfRep (x + y) = ((intOfRep x) + (intOfRep y)):=
  by
    unfold intOfRep
    apply Quotient.sound
    simp only [(· + ·)]
    unfold IntRep.add
    unfold Add.add
    unfold instAddIntRep
    simp
    unfold IntRep.add
    rfl

theorem mul_mk ( x y : IntRep ) :
  intOfRep (x * y) = ((intOfRep x) * (intOfRep y)):=
  by
    unfold intOfRep
    apply Quotient.sound
    simp only [(· * ·)]
    unfold IntRep.mul
    unfold Mul.mul
    unfold instMulIntRep
    simp
    unfold IntRep.mul
    rfl

theorem mul_mk_nat ( x y : Nat ) :
  intOfNat (x * y) = ((intOfNat x) * (intOfNat y)):=
  by
    unfold intOfNat
    apply Quotient.sound
    simp only [(· * ·)]
    unfold IntRep.mul
    unfold Mul.mul
    unfold MyNat.instMulNat
    simp
    rw[MyNat.mul_zero]
    rw[MyNat.add_zero]
    rw[MyNat.mul_zero]
    rw[MyNat.zero_add]
    rw[MyNat.zero_mul]
    rfl

theorem mul_expands ( x y : IntRep) :
  x * y = x.mul y := rfl

theorem inteq_means_zero ( x : IntRep ) :
  (x.pos = x.neg) ↔ x ≈ IntRep.zero :=
  by
    unfold IntRep.zero
    simp only [(· ≈ ·)]
    unfold instHasEquivOfSetoid
    simp
    simp[Setoid.r]
    unfold IntRep.Equivalent
    rw[MyNat.add_zero]
    rw[MyNat.zero_add]

theorem inverse_nat ( x : Int ) :
  x + (Int.negate x) = .zero :=
  by
    refine Quotient.inductionOn x ?_
    intro a
    rw[<-intOfRep]
    rw[<-negate_mk]
    rw[<-add_mk a a.negate]
    dsimp [IntRep.negate]
    change (intOfRep (IntRep.add a a.negate)) = intOfNat MyNat.Nat.zero
    rw[IntRep.add]
    rw[IntRep.negate]
    dsimp [IntRep.negate]
    cases a with
    | mk pos neg =>
      rw[add_commutes]
      unfold intOfRep
      unfold intOfNat
      apply Quotient.sound
      simp only [(· ≈ · )]
      unfold instHasEquivOfSetoid
      simp
      simp[Setoid.r]
      unfold IntRep.Equivalent
      simp
      rw[MyNat.add_zero]
      rw[MyNat.zero_add]

def Int.Divides ( a b : Int ) : Prop :=
  ∃ k : Int, b = a * k

def Int.Prime (p : Int) : Prop :=
  (p ≠ one) ∧ ∀ k : Int, (Divides k p) → (k = one ∨ k = p)

def Int.Even ( n : Int ) : Prop :=
  Int.Divides two n

def Int.Odd ( n : Int ) : Prop :=
  ∃ k : Int, n = two * k + one


end MyInt
