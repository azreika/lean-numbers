import Project1.Integers.Inequalities
import Project1.Integers.Arithmetic
import Project1.Nat.Parity
import Project1.Integers.Gcd

namespace MyInt
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

    have no_factors (p : Int) : (p.Divides d) → p = .one :=
      by
        intro p_divides_d
        sorry

    sorry

end MyInt
