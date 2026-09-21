import Project1.Nat.Nat

namespace MyNat

theorem add_zero (a : Nat) : a + .zero = a := by rfl

theorem succ_add (a b : Nat) :
  a + b.succ = (a + b).succ := by
    rfl

theorem zero_add (a : Nat) :
  .zero + a = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw[succ_add]
    rw[ih]

theorem mul_zero (a : Nat) : a * .zero = .zero := by rfl
theorem zero_mul (a : Nat) :
  .zero * a = .zero := by
    induction a with
    | zero => rfl
    | succ a ih =>
      change .zero + (.zero * a) = .zero
      rw[zero_add]
      rw[ih]

theorem add_one(a : Nat):
  (Nat.succ a) = Nat.one + a := by
    induction a with
    | zero => rfl
    | succ a ih =>
      rw[succ_add]
      rw[ih]

theorem succ_add_rev(a b : Nat) :
  a.succ + b = (a + b).succ := by
    induction b with
      | zero => rfl
      | succ b ih =>
        change a.succ + b.succ = (a + b.succ).succ
        change a.succ + b.succ = (a + b).succ.succ
        rw[succ_add]
        rw[ih]

theorem succ_commutes (a b : Nat) :
  a + b.succ = a.succ + b := by
    induction a with
    | zero =>
      rw[succ_add]
      rw[zero_add]
      rw[add_one]
      rfl
    | succ a ih =>
      rw[succ_add]
      rw[<-ih]
      rw[add_one]
      rw[ih]
      rw[<-add_one]
      rw[succ_add_rev]
      rw[succ_add_rev]
      rw[succ_add_rev]

theorem add_commutes (a b : Nat) :
  (a + b) = (b + a) := by
  induction a with
  | zero =>
    rw[zero_add]
    rfl
  | succ a ih =>
    rw[succ_add]
    rw[<-succ_commutes]
    rw[<-ih]
    rw[succ_add]

theorem succ_distributes (a b : Nat) :
  a * b.succ = a * b + a := by
  induction a with
  | zero =>
    rw[zero_mul]
    rw[zero_mul]
    rw[zero_add]
  | succ a ih =>
    change a.succ * b.succ = a.succ * b + a.succ
    rw[add_commutes]
    change a.succ * b.succ = a.succ + a.succ * b
    change a.succ + a.succ * b = a.succ + a.succ * b
    rfl

theorem add_associates (a b c: Nat) :
  (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
    rw[add_zero]
    rw[add_zero]
  | succ c ih =>
    rw[succ_add]
    rw[succ_add]
    rw[succ_add]
    rw[ih]

theorem mul_add_distributes ( a b c : Nat ) :
  a * (b + c) = a * b + a * c := by
  induction b with
  | zero =>
    rw[zero_add]
    rw[mul_zero]
    rw[zero_add]
  | succ b ih =>
    rw[succ_add_rev]
    rw[succ_distributes]
    rw[ih]
    change a * b + a * c + a = a * b.succ + a * c
    rw[succ_distributes]
    change ((a * b) + a * c) + a = ((a * b) + a) + a * c
    rw[add_associates]
    rw[add_associates]
    change (a * b) + (a * c + a) = (a * b) + (a + a * c)
    rw[add_commutes a]

theorem mul_associates ( a b c : Nat ) :
  (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rw[mul_zero]
    rw[mul_zero]
    rw[mul_zero]
  | succ c ih =>
    change (a * b * c.succ) = a * (b * c.succ)
    rw[succ_distributes]
    rw[succ_distributes]
    rw[mul_add_distributes]
    rw[ih]

end MyNat
