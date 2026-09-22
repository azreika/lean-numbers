import Project1.IntReps.IntRep

namespace MyInt

def IntRep.lte (x y : IntRep) : Prop :=
  MyNat.Nat.lte (x.pos + y.neg) (y.pos + x.neg)

theorem lte_respects_left (a1 a2 b : IntRep) (h1: a1 ≈ a2) :
  (a1.lte b = a2.lte b) :=
  by
    have h2 := unfold_intrep_equiv a1 a2 h1
    unfold IntRep.Equivalent at h2
    apply propext
    constructor
    intro h
    unfold IntRep.lte
    unfold IntRep.lte at h

    sorry
    intro h
    sorry
    -- unfold IntRep.lte
    -- cases b with
    -- | mk xpos xneg =>
    -- simp
    -- sorry

theorem lte_respects_right (a b1 b2 : IntRep) (h1: b1 ≈ b2) :
  (a.lte b1 = a.lte b2) := sorry

end MyInt
