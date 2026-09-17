import Project1.Nat.Nat
import Project1.Nat.Arithmetic

namespace MyInt

abbrev Nat := MyNat.Nat
abbrev add_commutes := MyNat.add_commutes
abbrev add_associates := MyNat.add_associates

-- want to represent as an equivalence class
-- represents pos - neg
structure IntRep where
  pos : Nat
  neg : Nat

-- since a - b = c - d <=> a + d = c + b
def IntRep.Equivalent ( x y : IntRep ) : Prop :=
  x.pos + y.neg = y.pos + x.neg

-- Need to prove its an equivalence relation
theorem equi_refl ( x : IntRep ) : IntRep.Equivalent x x :=
  by
    unfold IntRep.Equivalent
    rfl

theorem equi_symm ( x y : IntRep ) (h1 : x.Equivalent y) :
  (y.Equivalent x):=
  by
    unfold IntRep.Equivalent
    unfold IntRep.Equivalent at h1
    exact h1.symm

theorem equi_trans (x y z : IntRep)
    ( h1 : IntRep.Equivalent x y )
    ( h2 : IntRep.Equivalent y z ) :
  (IntRep.Equivalent x z) :=
  by
    unfold IntRep.Equivalent
    unfold IntRep.Equivalent at h1
    unfold IntRep.Equivalent at h2
    have h3 := MyNat.add_right_congr (x.pos + y.neg) (y.pos + x.neg) (y.pos + z.neg) h1
    rw (occs := .pos [3]) [add_commutes] at h3
    rw (occs := .pos [1]) [<-add_associates] at h3
    rw (occs := .pos [3]) [add_commutes] at h3
    rw[add_associates] at h3
    rw[add_associates] at h3
    rw (occs := .pos [2]) [<-add_associates] at h3
    rw[<-add_associates] at h3
    rw[add_commutes] at h3
    rw[add_associates] at h3
    have h4 := MyNat.add_left_cancel (c := y.pos) (y.neg + (x.pos + z.neg)) (x.neg + (y.pos + z.neg)) h3
    rw[add_commutes] at h4
    rw[h2] at h4
    rw (occs := .pos [1]) [<-add_associates] at h4
    have h5 := MyNat.add_right_cancel (x.pos + z.neg) (x.neg + z.pos) (y.neg) h4
    rw (occs := .pos [2]) [add_commutes] at h5
    exact h5

instance intRepSetoid : Setoid IntRep where
  r := IntRep.Equivalent
  iseqv := {
    refl := equi_refl,
    symm := @equi_symm,
    trans := @equi_trans,
  }

def IntRep.add ( x y : IntRep ) : IntRep :=
  IntRep.mk (x.pos + y.pos) (x.neg + y.neg)

def IntRep.negate ( x : IntRep ) : IntRep :=
  IntRep.mk x.neg x.pos

def Int :=
  Quotient intRepSetoid

def intOfRep ( r : IntRep ) : Int :=
  Quotient.mk intRepSetoid r

def intOfNat ( n : Nat ) : Int :=
  intOfRep (IntRep.mk n .zero )

theorem negate_respects ( a b : IntRep ) ( h : a.Equivalent b ) :
  (a.negate.Equivalent b.negate) := by sorry


theorem add_respects_right ( a b c : IntRep ) ( h : a.Equivalent b ) :
  (a.add c).Equivalent (b.add c) := by sorry

theorem add_respects_left ( a b c : IntRep ) ( h : a.Equivalent b ) :
  (c.add a).Equivalent (c.add b) := by sorry

def Int.negate : Int -> Int :=
  Quotient.lift
    (fun x => Quotient.mk intRepSetoid (IntRep.negate x))
    (by
      intro a b h
      apply Quotient.sound
      exact negate_respects a b h
    )

def Int.add : Int -> Int -> Int :=
  Quotient.lift
  ( fun x => Quotient.lift
      ( fun y => Quotient.mk intRepSetoid (IntRep.add x y))
      (by
        intro a b h
        apply Quotient.sound
        sorry
      )
  ) (by
    intro a b h
    funext y
    sorry
  )

instance : Add IntRep where
  add := IntRep.add

instance : Add Int where
  add := Int.add

def zero_int_rep := IntRep.mk .zero .zero

def zero := intOfRep zero_int_rep

theorem negate_mk ( x : IntRep ) :
  intOfRep (x.negate) = (Int.negate (intOfRep x)):=
  by sorry

theorem add_mk ( x y : IntRep ) :
  intOfRep (x + y) = ((intOfRep x) + (intOfRep y)):=
  by sorry

theorem inteq_means_zero ( x : IntRep ) ( h1 : x.pos = x.neg ) :
  x = zero_int_rep := by
  sorry

theorem inverse_nat ( x : Int ) :
  x + (Int.negate x) = zero :=
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
      dsimp [IntRep.add]
      rw[add_commutes]
      have h1 := inteq_means_zero (IntRep.mk (neg + pos) (neg + pos))
      dsimp [IntRep.add] at h1
      have h2 :(neg + pos) = (neg+pos) := by rfl
      have h3 := h1 h2
      unfold zero_int_rep at h3
      rw[h3]
      rfl

end MyInt
