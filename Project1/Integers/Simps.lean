import Project1.Integers.Arithmetic
import Project1.IntReps.Inequalities
import Project1.Nat.Properties

namespace MyInt

theorem negate_twice (a : Int) : (a.negate.negate = a) :=
  by
    refine Quotient.inductionOn a ?_
    intro a
    rw[<-intOfRep]
    rw[<-negate_mk]
    rw[<-negate_mk]
    rfl

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

@[simp] theorem one_plus_one_is_two_1 : (Int.one + Int.one = Int.two) := by
  rfl

@[simp] theorem one_plus_one_is_two_2 (a : Int) : ((a +Int.one) + Int.one = a + Int.two) := by
  rw[int_add_associates]
  rfl

@[simp] theorem two_minus_one_is_one1 : (Int.two + Int.one.negate = Int.one) := by
  apply add_right_cancel (c:=Int.one)
  rw[int_add_associates]
  simp

@[simp] theorem negate_negate_is_pos (a: Int) :  a.negate.negate = a :=
  by
    exact negate_twice a

@[simp] theorem zero_neg_is_zero : Int.zero.negate = Int.zero :=
  by
    rfl

  @[simp] theorem mul_neg_one1 (a : Int) : a * Int.one.negate = a.negate :=
  by
    rw[<-neg_expands_mul]
    simp

  @[simp] theorem mul_neg_one2 (a : Int) : Int.one.negate * a = a.negate :=
  by
    rw[int_mul_commutes]
    rw[<-neg_expands_mul]
    simp

end MyInt
