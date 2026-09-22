import Project1.Nat.Nat
import Project1.Nat.Properties

namespace MyInt

abbrev Nat := MyNat.Nat
abbrev add_commutes := MyNat.add_commutes
abbrev add_associates := MyNat.add_associates
abbrev mul_commutes := MyNat.mul_commutes

-- want to represent as an equivalence class
-- represents pos - neg
structure IntRep where
  pos : MyNat.Nat
  neg : MyNat.Nat


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

def IntRep.mul ( x y : IntRep ) : IntRep :=
  IntRep.mk ((x.pos * y.pos) + (x.neg * y.neg)) ((x.pos * y.neg) + (x.neg * y.pos))

def IntRep.negate ( x : IntRep ) : IntRep :=
  IntRep.mk x.neg x.pos

theorem unfold_intrep_equiv (a b : IntRep) (h1: a ≈ b) :
  a.Equivalent b :=
  by
    simp only [(· ≈ · )] at h1
    unfold instHasEquivOfSetoid at h1
    simp at h1
    simp[Setoid.r] at h1
    exact h1

theorem unfold_intrep_equiv_congr (a b : IntRep) (h1: a.Equivalent b) :
  (a ≈ b) :=
  by
    simp only [(· ≈ · )]
    unfold instHasEquivOfSetoid
    simp
    simp[Setoid.r]
    exact h1

theorem IntRep.equiv_def (a b : IntRep ) :
  a ≈ b ↔ IntRep.Equivalent a b := by rfl

end MyInt
