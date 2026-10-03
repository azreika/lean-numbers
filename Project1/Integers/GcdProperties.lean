import Project1.Integers.Inequalities
import Project1.Integers.Arithmetic
import Project1.Nat.Parity
import Project1.Integers.Gcd

namespace MyInt

def Int.Unit (a : Int) : Prop :=
  a.Divides .one

theorem one_is_unit_prop : Int.Unit .one :=
  by
    dsimp [Int.Unit]
    dsimp [Int.Divides]
    exists Int.one

theorem all_div_one_means_unit (a : Int) (h1: ∀ (p : Int), p.Divides a → Int.Unit p) :
  a.Unit := by
    sorry

theorem unit_means_one_or_negone ( a : Int ) (h1 : a.Unit) : (a = .one ∨ a = Int.one.negate) :=
  by
    sorry

theorem gcd_gt_zero (a b d : Int) (h1 : d = Int.gcd a b) : d > .zero :=
  by
    dsimp [Int.gcd] at h1
    sorry

theorem lt_both_impossible (a b : Int) (h1: a < b) (h2 : b < a) : False :=
  by
    sorry

theorem chap1_q10 (u v : Int) (h1 : Int.gcd u v = .one) :
  (Int.gcd (u + v) (u -v)) = .one ∨
  (Int.gcd (u + v) (u-v)) = .two :=
  by
    let d := Int.gcd (u + v) (u-v)
    have hd : d = Int.gcd (u + v) (u -v ) := rfl
    rw[<-hd]

    by_cases d_is_one : (d = Int.two)
    right
    exact d_is_one

    left

    have no_factors (p : Int) : (p.Divides d) → Int.Unit p :=
      by
        intro p_divides_d
        sorry

    have h2 := all_div_one_means_unit d no_factors
    have h3 := unit_means_one_or_negone d h2
    by_cases h4 : d ≠ Int.one
    have h5 := Or.elim h3 h4
    simp at h5

    have h6 := gcd_gt_zero (u+v) (u-v) d hd
    have h7 : (Int.one.negate < Int.zero) := by
      sorry

    rw[<-h5] at h7
    have h8 := lt_both_impossible d Int.zero h7 h6
    contradiction

    simp at h4
    exact h4

end MyInt
