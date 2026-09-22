import Project1.IntReps.IntRep

namespace MyInt

def IntRep.lte (x y : IntRep) : Prop :=
  MyNat.Nat.lte (x.pos + y.neg) (y.pos + x.neg)

theorem nat_rearrange_add (a b c : Nat) :
  (a + b) + c = (a + c) + b := by
    rw[add_associates]
    rw (occs := .pos [2]) [add_commutes]
    rw[<-add_associates]

theorem lte_left_lemma (a1 a2 b : IntRep) (h1 : a1 ≈ a2) :
  (a1.lte b → a2.lte b) :=
  by
    intro h
    dsimp [IntRep.lte]
    dsimp [IntRep.lte] at h

    cases a1 with
    | mk m n =>
      cases a2 with
      | mk u v =>
        cases b with
        | mk b c =>
          simp
          simp at h
          have h2 := unfold_intrep_equiv (IntRep.mk m n) (IntRep.mk u v) h1
          dsimp[IntRep.Equivalent] at h2

          have h3 : (m + v + c) = (u + n + c) := MyNat.add_right_congr (m + v) (u + n) c h2

          have hlt : (m + v + c).lte (b + v + n) := by
            have h4 : ((m + c) + v).lte ((b + n) + v) := MyNat.lte_add_term (m + c) (b+n) v h
            rw[nat_rearrange_add] at h4
            rw (occs := .pos [2]) [nat_rearrange_add] at h4
            exact h4

          rw[h3] at hlt
          rw[MyNat.add_commutes] at hlt
          rw (occs := .pos [3] ) [MyNat.add_commutes] at hlt
          have hlt2 : ( u + c ).lte (b + v) := by
            rw[<-add_associates] at hlt
            rw[add_commutes] at hlt
            rw (occs := .pos [2]) [add_commutes] at hlt
            have h5 : (u + c).lte (b + v) := by
              exact MyNat.lte_remove_term_left (u + c) (b + v) n hlt
            exact h5
          exact hlt2

theorem lte_respects_left (a1 a2 b : IntRep) (h1: a1 ≈ a2) :
  (a1.lte b = a2.lte b) :=
  by
    apply propext
    constructor
    exact lte_left_lemma a1 a2 b h1
    exact lte_left_lemma a2 a1 b h1.symm

theorem lte_respects_right (a b1 b2 : IntRep) (h1: b1 ≈ b2) :
  (a.lte b1 = a.lte b2) :=
  by
    sorry

end MyInt
