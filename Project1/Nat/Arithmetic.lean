import Project1.Nat.Nat

namespace MyNat

-- Basic laws
theorem add_zero (a : Nat) : a + .zero = a := by rfl
theorem mul_zero (a : Nat) : a * .zero = .zero := by rfl

theorem zero_add (a : Nat) :
  .zero + a = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change (.zero + a).succ = a.succ
    rw[ih]

theorem succ_add (a b : Nat) :
  a + b.succ = (a + b).succ := by
    rfl

theorem add_one(a : Nat):
  (Nat.succ a) = Nat.one + a := by
    induction a with
    | zero =>
      rfl
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

theorem zero_mul (a : Nat) :
  .zero * a = .zero := by
    induction a with
    | zero => rfl
    | succ a ih =>
      change .zero * a.succ = .zero
      change .zero + (.zero * a) = .zero
      rw[zero_add]
      rw[ih]

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
