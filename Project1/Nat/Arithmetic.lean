import Project1.Nat.Nat
import Project1.Nat.Fundamentals

namespace MyNat

-- Basic laws
theorem mul_one (a : Nat) :
  a * .one = a := by
    rfl

theorem one_mul(a : Nat):
  .one * a = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change .one * a.succ = a.succ
    change .one + (.one * a) = a.succ
    rw[ih]
    rw[add_one]

instance : LE Nat where
  le := Nat.lte

theorem zero_is_min ( a : Nat ) (h1 : Nat.lte a .zero ) :
  (a = .zero) :=
  by
    cases a with
    | zero => rfl
    | succ a => cases h1

theorem succ_same ( a b : Nat ) (h1: a = b) :
  (a.succ = b.succ) :=
  by
    induction a with
    | zero =>
      rw[h1]
    | succ a ih =>
      rw[h1]

theorem succ_same_rev ( a b : Nat ) (h1: a.succ = b.succ) :
  (a = b) :=
  by
    induction a with
    | zero =>
      cases h1
      rfl
    | succ a ih =>
      cases h1
      rfl

theorem succ_distributes_rev (a b : Nat) :
  a.succ * b = a * b + b := by
  induction b with
  | zero =>
    rw[add_zero]
    rw[mul_zero]
    rw[mul_zero]
  | succ b ih =>
    rw[succ_distributes]
    rw[ih]
    rw[succ_distributes]
    rw[succ_add]
    rw[succ_add]
    change (((a * b) + b) + a).succ = (((a * b) + a) + b).succ
    rw[add_associates]
    rw[add_associates]
    change ((a * b) + (b + a)).succ = ((a * b) + (a + b)).succ
    rw[add_commutes a b]

theorem mul_commutes(a b : Nat) :
  (a * b) = (b * a) := by
  induction b with
  | zero =>
    rw[zero_mul]
    rfl
  | succ b ih =>
    rw[succ_distributes]
    rw[ih]
    rw[add_commutes]
    rw[succ_distributes_rev]
    rw[<-ih]
    rw[add_commutes]


theorem add_right_cancel ( a b c : Nat ) ( h1 : a + c = b + c ) :
  a = b := by
  induction c generalizing a b with
  | zero =>
    rw[add_zero] at h1
    rw[add_zero] at h1
    exact h1
  | succ c ih =>
    have h3 := ih a b
    rw[succ_add] at h1
    rw[succ_add] at h1
    have h4 := succ_same_rev (a+c) (b+c) h1
    exact h3 h4

theorem add_right_congr ( a b c : Nat ) ( h1 : a = b ) :
  (a + c = b + c) :=
  by
    induction c generalizing a b with
    | zero =>
      rw[add_zero]
      rw[add_zero]
      exact h1
    | succ c ih =>
      rw[succ_add]
      rw[succ_add]
      rw[succ_same]
      have h2 := ih a b h1
      exact h2

theorem add_left_congr ( a b c : Nat ) ( h1 : a = b ) :
  (c + a = c + b) :=
  by
    induction c generalizing a b with
    | zero =>
      rw[zero_add]
      rw[zero_add]
      exact h1
    | succ c ih =>
      rw[add_commutes]
      rw[succ_add]
      rw (occs := .pos [2]) [add_commutes]
      rw[succ_add]
      rw[succ_same]
      have h2 := ih a b h1
      rw[add_commutes]
      rw (occs := .pos [2]) [add_commutes]
      exact h2

theorem add_left_cancel ( a b c : Nat ) ( h1 : c + a = c + b ) :
  a = b := by
  induction c generalizing a b with
  | zero =>
    rw[zero_add] at h1
    rw[zero_add] at h1
    exact h1
  | succ c ih =>
    have h3 := ih a b
    rw[add_commutes] at h1
    rw[succ_add] at h1
    rw (occs := .pos [2]) [add_commutes] at h1
    rw[succ_add] at h1
    have h4 := succ_same_rev (a+c) (b+c) h1
    rw[add_commutes] at h4
    rw (occs := .pos [2]) [add_commutes] at h4
    exact h3 h4

end MyNat
