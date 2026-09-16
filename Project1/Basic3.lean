namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat

-- Addition
def Nat.add : Nat -> Nat -> Nat
  | a, .zero => a
  | a, .succ b => .succ (add a b)

instance : Add Nat where
  add := Nat.add

-- Greater than
def Nat.lte : Nat -> Nat -> Prop
  | .zero, _ => true
  | _, .zero  => false
  | .succ a, .succ b => lte a b

def Nat.lt (a b : Nat) : Prop :=
  Nat.lte a b ∧ a ≠ b

-- Multiplication
def Nat.mul : Nat -> Nat -> Nat
  | _, .zero => .zero
  | a, .succ b => a + (mul a b)

instance : Mul Nat where
  mul := Nat.mul

-- Basic laws
theorem add_zero (a : Nat) :
  a + .zero = a := by
    rfl

theorem mul_zero (a : Nat) :
  a * .zero = .zero := by
    rfl

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

def Nat.one : Nat := (Nat.succ Nat.zero)
def Nat.two : Nat := (Nat.succ Nat.one)

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

def Nat.Divides ( a b : Nat ) : Prop :=
  ∃ k : Nat, b = a * k

def Nat.Prime (p : Nat) : Prop :=
  (p ≠ .one) ∧ ∀ k : Nat, (Divides k p) → (k = .one ∨ k = p)

example : ¬(Nat.Prime .one) := by
  intro h
  exact h.1 rfl

theorem self_dividing ( a : Nat ) :
  Nat.Divides a a := by
  unfold Nat.Divides
  exists Nat.one

theorem divides_transitive (a b c : Nat) (h1: Nat.Divides a b) (h2: Nat.Divides b c) :
  Nat.Divides a c := by
  unfold Nat.Divides
  unfold Nat.Divides at h1
  obtain ⟨ k, hk ⟩ := h1
  unfold Nat.Divides at h2
  obtain ⟨ j, hj ⟩  := h2
  exists j*k
  rw[mul_commutes]
  rw[mul_associates]
  rw[mul_commutes]
  rw[mul_commutes k]
  rw[<-hk]
  rw[<-hj]

theorem one_divides ( a : Nat) :
  Nat.Divides .one a := by
    unfold Nat.Divides
    exists a
    rw[one_mul]

theorem divides_zero ( a : Nat ) :
  Nat.Divides a .zero := by
    unfold Nat.Divides
    exists .zero

def Nat.Even ( n : Nat ) : Prop :=
  Nat.Divides Nat.two n

def Nat.Odd ( n : Nat ) : Prop :=
  ∃ k : Nat, n = Nat.two * k + Nat.one

theorem two_is_even : (Nat.Even .two) := by
  unfold Nat.Even
  unfold Nat.Divides
  exists .one

theorem odd_succ_is_even (a : Nat) (h1: Nat.Odd a) :
  Nat.Even a.succ := by
  unfold Nat.Even
  unfold Nat.Divides
  unfold Nat.Odd at h1
  obtain ⟨ k, hk1 ⟩ := h1
  rw[hk1]
  rw[<-succ_add]
  rw[<-Nat.two]
  exists .succ k
  rw (occs := .pos [2]) [<- mul_one Nat.two]
  rw[<-mul_add_distributes]
  rw[add_commutes]
  rw[add_one]

theorem even_succ_is_odd (a : Nat) (h1: Nat.Even a) :
  Nat.Odd a.succ := by
  unfold Nat.Odd

  unfold Nat.Even at h1
  obtain ⟨ k1, hk1 ⟩ := h1

  exists k1
  rw[<-hk1]
  rw[add_one]
  rw[add_commutes]

theorem odd_or_even (n : Nat) :
  Nat.Odd n ∨ Nat.Even n := by
  induction n with
  | zero =>
    right
    unfold Nat.Even
    apply divides_zero
  | succ n ih =>
    cases ih with
    | inl hOdd =>
      right
      apply odd_succ_is_even
      apply hOdd
    | inr hEven =>
      left
      apply even_succ_is_odd
      apply hEven

noncomputable
def Nat.half (a : Nat) (h : Nat.Even a) : Nat :=
  by
    unfold Nat.Even at h
    unfold Nat.Divides at h
    exact Exists.choose h

theorem succed_is_nonzero (a : Nat) : (Nat.succ a ≠ .zero) := by
    intro h
    cases h

theorem plus_two ( a : Nat ) :
  a.succ.succ = a + .two :=
  by
    rw[add_one]
    rw[add_one]
    rw[<-add_associates]
    rw[<-add_one]
    rw[<-Nat.two]
    rw[add_commutes]

theorem zero_from_mulzero ( a b : Nat ) ( h1: a * b = .zero) :
  (a = .zero ∨ b = .zero) := by sorry

theorem nat_ordered ( a b : Nat ) :
  (a = b) ∨ (Nat.lt a b) ∨ (Nat.lt b a) :=
  by
    sorry

theorem ineq_one_adds (a b : Nat ) (h1 : Nat.lt a b ) :
  (Nat.lt (a+.one) (b+.one)) :=
  by sorry

theorem add_term_ineq ( a b c : Nat ) (h1 : Nat.lt a b ) :
  Nat.lt (a + c) (b + c ) := by
    induction c with
    | zero =>
      rw[add_zero]
      rw[add_zero]
      exact h1
    | succ c ih =>
      rw[add_one]
      rw (occs := .pos [2]) [add_commutes]
      rw[<-add_associates]
      rw (occs := .pos [4]) [add_commutes]
      rw[<-add_associates]
      have h2 : (Nat.lt ((a + c) + .one) ((b + c) + .one)) := ineq_one_adds (a+c) (b+c) ih
      exact h2

theorem add_inequalities ( a b c d : Nat ) (h1 : Nat.lt a b) (h2 : Nat.lt c d ) :
  Nat.lt (a + c) (b + d) := by
    sorry

theorem mult_matches ( a b c : Nat ) (h1 : Nat.lt a b ) (h2 : c ≠ .zero) :
  Nat.lt (a * c) (b * c) :=
  by
    cases c with
    | zero => simp at h2
    | succ c =>
      induction c with
      | zero =>
        rw[add_one]
        rw[mul_add_distributes]
        rw[mul_zero]
        rw[add_zero]
        rw[mul_one]
        rw[add_zero]
        rw[mul_one]
        exact h1
      | succ c ih =>
        rw[add_one]
        rw[mul_add_distributes]
        have h3: c.succ ≠ .zero := succed_is_nonzero c
        have h4: Nat.lt (a * c.succ) (b*c.succ) := ih h3
        rw[mul_one]
        rw[mul_add_distributes]
        rw[mul_one]
        have h5: Nat.lt (a + a * c.succ) (b + b * c.succ) :=
          add_inequalities a b (a * c.succ) (b*c.succ) h1 h4
        exact h5

theorem lt_means_neq ( a b : Nat ) ( h1: Nat.lt a b ) :
  (a ≠ b) :=
  by
    unfold Nat.lt at h1
    have h2 : a ≠ b := h1.right
    exact h2

theorem div_cancels (a b c : Nat) (h1: c ≠ .zero) (h2: a * c = b * c) :
  a = b :=
  by
    have h3 := nat_ordered a b
    cases h3 with
    | inl heq =>
      exact heq
    | inr hneq =>
      cases hneq with
      | inl hlt =>
        have h4: Nat.lt (a * c) (b*c) := mult_matches a b c hlt h1
        have h5: (a * c) ≠ (b*c) := lt_means_neq (a*c) (b*c) h4
        have bad : False := h5 h2
        exact False.elim bad
      | inr hrt =>
        have h4: Nat.lt (b * c) (a*c) := mult_matches b a c hrt h1
        have h5: (b * c) ≠ (a*c) := lt_means_neq (b*c) (a*c) h4
        have bad : False := h5 h2.symm
        exact False.elim bad


-- theorem odd_squared ( n : Nat ) ( h1 : Nat.Odd n ) :
--   Nat.Odd (n * n) := by
--   unfold Nat.Odd
--   unfold Nat.Odd at h1
--   obtain ⟨ k, hk ⟩ := h1
--   exists .two * k * k + .two * k
--   rw[hk]
--   rw[mul_add_distributes]
--   rw[mul_add_distributes]
--   rw[mul_one]
--   rw[mul_commutes]
--   rw[mul_add_distributes]
--   rw[mul_associates]
--   rw[mul_associates]
--   rw[mul_associates Nat.two k]
--   rw[mul_commutes Nat.two k]





-- def Rational (x: ℝ) := ∃ (p q : Nat), x = p/q

-- def Irrational (x: ℝ) := x ∉ Rational

-- we want to eventually prove that root 2 is irrational

end MyNat
