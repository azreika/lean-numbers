import Project1.Nat.Nat
import Project1.Nat.Arithmetic

open Classical

namespace MyNat

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

theorem eq_or_not ( a b : Nat ) :
  (a = b) ∨ (a ≠ b) :=
  by
    exact Classical.em (a = b)

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

theorem succ_is_different (a : Nat) :
  a ≠ a.succ :=
  by
    induction a with
    | zero =>
      have h2 := succed_is_nonzero .zero
      exact h2.symm
    | succ a ih =>
      cases eq_or_not a.succ a.succ.succ with
      | inl hl =>
        cases hl
      | inr hr =>
        exact hr

theorem succ_is_geq ( a : Nat ) :
  Nat.lte a ( a + .one ) :=
  by
    rw[Nat.one]
    rw[succ_add]
    rw[add_zero]
    induction a with
    | zero => rfl
    | succ a ih => exact ih

theorem succ_is_more (a : Nat) :
  Nat.lt a (a + .one) :=
  by
    unfold Nat.lt
    have h1 : Nat.lte a ( a + .one):= succ_is_geq a
    have h2 : a ≠ a.succ := succ_is_different a
    rw[add_one] at h2
    rw[add_commutes] at h2
    exact And.intro h1 h2

theorem gte_zero ( a : Nat ) :
  Nat.lte .zero a :=
  by
    induction a with
    | zero =>
      unfold Nat.lte
      rfl
    | succ a ih =>
      exact ih

theorem leq_itself ( a : Nat ) :
  (Nat.lte a a ) :=
  by
    induction a with
    | zero =>
      rfl
    | succ a ih =>
      exact ih

theorem eq_means_leq ( a b : Nat ) (h1 : a = b ) :
  (Nat.lte a b ) :=
  by
    induction a with
    | zero => rfl
    | succ a ih =>
      change a.succ.lte b
      cases b with
      | zero =>
        have h2 : a.succ ≠ .zero := succed_is_nonzero a
        have h3 := And.intro h1 h2
        simp at h3
      | succ b =>
        cases h1
        change a.succ.lte a.succ
        change a.lte a
        have h2 := leq_itself a
        exact h2

theorem lt_means_lte (a b : Nat) (h1 : Nat.lt a b) :
  (Nat.lte a b ) :=
  by
    unfold Nat.lt at h1
    exact h1.left

theorem nat_ordered_lte ( a b : Nat ) :
  (Nat.lte a b ) ∨ (Nat.lte b a ) :=
  by
    induction b generalizing a with
    | zero =>
      have h1 := gte_zero a
      right
      exact h1
    | succ b ih =>
      cases a with
      | zero =>
        have h2 := gte_zero b.succ
        left
        exact h2
      | succ a =>
        change a.succ.lte b.succ ∨ b.succ.lte a.succ
        change a.lte b ∨ b.lte a
        exact ih a

theorem nat_ordered ( a b : Nat ) :
  (a = b) ∨ (Nat.lt a b) ∨ (Nat.lt b a) :=
  by
    have h1 := nat_ordered_lte a b
    cases eq_or_not a b with
    | inl hl1 =>
      left
      exact hl1
    | inr hr1 =>
      right
      unfold Nat.lt
      cases h1 with
      | inl hl2 =>
        left
        exact And.intro hl2 hr1
      | inr hr2 =>
        right
        exact And.intro hr2 hr1.symm

theorem lte_trans (a b c : Nat) (h1 : Nat.lte a b) (h2 : Nat.lte b c) :
  (Nat.lte a c) :=
  by
    induction a generalizing b c with
    | zero =>
      have h3 := gte_zero c
      exact h3
    | succ a ih =>
      cases c with
      | zero =>
        have h3 : b = .zero := zero_is_min b h2
        rw[h3] at h1
        have h4 : a.succ = .zero := zero_is_min a.succ h1
        have h5 := succed_is_nonzero a
        have h6 := And.intro h4 h5
        simp at h6
      | succ c =>
        change a.lte c
        have h3 := ih b c
        cases b with
        | zero =>
          have h4 := succed_is_nonzero a
          cases h1
        | succ b =>
          change a.lte b at h1
          change b.lte c at h2
          exact ih b c h1 h2

theorem add_is_more ( a b : Nat ) :
  (Nat.lte a (a + b)) :=
  by
    induction a generalizing b with
    | zero =>
      have h1 := gte_zero (Nat.zero + b)
      exact h1
    | succ a ih =>
      rw[add_commutes]
      rw[succ_add]
      change a.lte (b+a)
      rw[add_commutes]
      exact ih b

theorem zero_from_mulzero ( a b : Nat ) ( h1: a * b = .zero) :
  (a = .zero ∨ b = .zero) :=
  by
    cases eq_or_not a .zero with
    | inl hl =>
      left
      exact hl
    | inr hr =>
      cases b with
      | zero =>
        right
        rfl
      | succ b =>
        right
        rw[add_one] at h1
        rw[mul_add_distributes] at h1
        rw[mul_one] at h1
        have h4 := add_is_more a (a*b)
        rw[h1] at h4
        have h5 := zero_is_min a h4
        have h6 := And.intro hr h5
        simp at h6

theorem succ_add_one ( a : Nat ) :
  (a.succ = a + .one) :=
  by
    rw[Nat.one]
    rw[succ_add]
    rw[add_zero]

theorem lte_one_adds (a b : Nat ) (h1 : Nat.lte a b ) :
  (Nat.lte (a+.one) (b+.one)) :=
  by
    rw[<-succ_add_one]
    rw[<-succ_add_one]
    induction a generalizing b with
    | zero => exact h1
    | succ a ih =>
      change a.succ.lte b
      exact h1

theorem lte_one_minus (a b : Nat ) (h1 : Nat.lte (a + .one) (b+.one) ) :
  (Nat.lte a b) :=
  by
    rw[<-succ_add_one] at h1
    rw[<-succ_add_one] at h1
    change a.succ.lte b.succ
    change a.lte b
    exact h1

theorem lte_add_term ( a b c : Nat ) (h1 : Nat.lte a b ) :
  Nat.lte (a + c) (b + c) := by
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
      have h2 : (Nat.lte ((a + c) + .one) ((b + c) + .one)) := lte_one_adds (a+c) (b+c) ih
      exact h2

theorem lte_cancel_right ( a b c : Nat ) (h1 : Nat.lte (a + c) (b +c) ) :
    Nat.lte a b := by
    induction c generalizing a b with
    | zero =>
      rw[add_zero] at h1
      rw[add_zero] at h1
      exact h1
    | succ c ih =>
      rw[succ_add_one] at h1
      rw[<-add_associates] at h1
      rw[<-add_associates] at h1
      have h2 := lte_one_minus (a + c) (b+c) h1
      have h3 := ih a b h2
      exact h3

theorem lt_means_neq ( a b : Nat ) ( h1: Nat.lt a b ) :
  (a ≠ b) :=
  by
    unfold Nat.lt at h1
    have h2 : a ≠ b := h1.right
    exact h2

theorem add_neq ( a b c : Nat ) ( h1 : a ≠ b ) :
  (a + c ≠ b + c) :=
  by
    intro h2
    have h3 := add_right_cancel a b c h2
    have bad := And.intro h1 h3
    simp at bad

theorem lt_add_term ( a b c : Nat ) (h1 : Nat.lt a b ) :
  Nat.lt (a + c) (b + c) :=
  by
    have h2 := lt_means_lte a b h1
    have h3 := lte_add_term a b c h2
    unfold Nat.lt
    have h4 : (a ≠ b) := lt_means_neq a b h1
    have h5 := add_neq a b c h4
    exact (And.intro h3 h5)

theorem lte_cases ( a b : Nat ) (h1 : Nat.lte a b ) :
  (a = b) ∨ (Nat.lt a b) :=
  by
    unfold Nat.lt
    have h2: (a = b) ∨ (a ≠ b) := eq_or_not a b
    cases h2 with
    | inl hl =>
      left
      exact hl
    | inr hr =>
      right
      exact And.intro h1 hr

theorem lte_antisym ( a b : Nat ) (h1 : Nat.lte a b ) (h2 : Nat.lte b a) :
  (a = b) := by
  induction a generalizing b with
  | zero =>
    have h3 := zero_is_min b h2
    exact h3.symm
  | succ a ih =>
    cases b with
    | zero =>
      have h3 := zero_is_min a.succ h1
      have h4 := succed_is_nonzero a
      have h5 := And.intro h3 h4
      simp at h5
    | succ b =>
      change a.lte b at h1
      change b.lte a at h2
      have h3 := ih b h1 h2
      have h4 := succ_same a b h3
      exact h4

theorem lt_oneway ( a b : Nat ) ( h1: Nat.lt a b) :
  (¬ Nat.lt b a) :=
  by
    intro h2
    have hab := h1.left
    have hba := h2.left
    have heq := lte_antisym a b hab hba
    have hno := h1.right
    have h5 := And.intro heq hno
    simp at h5

theorem lt_trans (a b c : Nat) (h1 : Nat.lt a b) (h2 : Nat.lt b c) :
  (Nat.lt a c ) := by
    have h3 := lt_means_lte a b h1
    have h4 := lt_means_lte b c h2
    have h5 := lte_trans a b c h3 h4
    unfold Nat.lt
    constructor
    exact h5
    intro h6
    rw[h6] at h1
    have h7 := lt_oneway c b h1
    have h8 := And.intro h2 h7
    simp at h8

theorem add_inequalities ( a b c d : Nat ) (h1 : Nat.lt a b) (h2 : Nat.lt c d ) :
  Nat.lt (a + c) (b + d) := by
    have h3 := lt_add_term a b c h1
    have h4 := lt_add_term c d b h2
    rw[add_commutes] at h4
    have h5 := lt_trans (a + c) (b + c) (d + b) h3 h4
    rw (occs := .pos [2]) [add_commutes]
    exact h5

theorem natural_gap ( a b : Nat ) ( h1 : Nat.lte a b ) :
  ∃ (m : Nat), a + m = b :=
  by
    induction b generalizing a with
    | zero =>
      cases a with
      | zero =>
        exists .zero
      | succ a =>
        have h2 : a.succ = .zero := zero_is_min a.succ h1
        rw[h2]
        exists(.zero)
    | succ b ih =>
      have h2 : (a = b.succ) ∨ (Nat.lt a b.succ) := lte_cases a b.succ h1
      cases h2 with
      | inl hl =>
        exists .zero
      | inr hr =>
        cases nat_ordered a b with
        | inl hl =>
          exists .one
          rw[Nat.one]
          rw[succ_add]
          rw[add_zero]
          have h2 : a.succ = b.succ := succ_same a b hl
          exact h2
        | inr hr2 =>
          cases hr2 with
          | inl hx1 =>
            unfold Nat.lt at hx1
            have h2 := ih a hx1.left
            obtain ⟨ k, hk2 ⟩ := h2
            exists (k + .one)
            rw[<-add_associates]
            rw[hk2]
            rw[add_one]
            rw[add_commutes]
          | inr hx2 =>
            cases a with
            | zero =>
              exists b.succ
              rw[zero_add]
            | succ a =>
              change a.lte b at h1
              have h4 := ih a h1
              obtain ⟨ m, hm2 ⟩ := h4
              have h5 := succ_same (a + m) b
              rw[add_commutes] at h5
              rw[<-succ_add] at h5
              rw[add_commutes] at h5
              have h6 := h5 hm2
              rw[add_commutes] at h6
              exists m

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

theorem div_cancels_left ( a b c : Nat ) (h1 : c ≠ .zero ) (h2 : c * a = c * b) :
  a = b :=
  by
    rw[mul_commutes] at h2
    rw (occs := .pos [2])  [mul_commutes] at h2
    have h3 := div_cancels a b c h1 h2
    exact h3

theorem mul_left ( a b c : Nat ) (h2 : a = b) :
  c * a = c * b :=
  by
    induction c generalizing a b with
    | zero =>
      rw[zero_mul]
      rw[zero_mul]
    | succ c ih =>
      rw[mul_commutes]
      rw (occs := .pos [2]) [mul_commutes]
      change a * c.succ = b * c.succ
      change a + (a * c) = b + (b * c)
      have h3 := ih a b h2
      rw[mul_commutes]
      rw (occs := .pos [2]) [mul_commutes]
      rw[h3]
      apply add_right_congr
      exact h2

theorem two_squared : (Nat.two * Nat.two = Nat.four) :=
  by
    rw[Nat.two]
    rw[Nat.one]
    rw[add_one]
    rw[add_one]
    rw[add_zero]
    rw[mul_add_distributes]
    rw[mul_one]
    rw[Nat.one]
    rw[succ_add]
    rw[add_zero]
    rw[succ_add]
    rw[succ_add]
    rw[add_zero]
    rw[<-Nat.one]
    rw[<-Nat.two]
    rw[<-Nat.three]
    rw[<-Nat.four]

theorem mul_rearrange (a b c : Nat) :
  (a * (b * c)) = c * (a * b) :=
  by
    rw[<-mul_associates]
    rw[mul_commutes]

theorem odd_squared ( n : Nat ) ( h1 : Nat.Odd n ) :
  Nat.Odd (n * n) := by
  unfold Nat.Odd
  unfold Nat.Odd at h1
  obtain ⟨ k, hk ⟩ := h1
  exists .two * k * k + .two * k
  rw[hk]
  rw[mul_add_distributes]
  rw[mul_add_distributes]
  rw[mul_one]
  rw[mul_commutes]
  rw[mul_add_distributes]
  rw[mul_associates]
  rw[mul_associates]
  rw[mul_associates Nat.two k]
  rw[mul_commutes Nat.two k]
  rw[mul_rearrange]
  rw[mul_rearrange]
  rw[mul_associates]
  rw[two_squared]
  rw[<-mul_associates]
  rw[mul_one]
  rw[<-mul_associates]
  rw[two_squared]
  rw[mul_rearrange]
  rw[mul_rearrange]
  rw[mul_associates]
  rw[add_associates]
  rw[add_associates]
  apply add_left_congr
  rw[<-add_associates]
  apply add_right_congr
  rw[mul_rearrange]
  rw[<-mul_associates]
  rw[Nat.two]
  rw[Nat.one]
  rw[add_one]
  rw[mul_add_distributes]
  rw[mul_add_distributes]
  rw[add_one]
  rw[add_zero]
  rw[mul_one]
  rw[mul_one]
  rw[mul_commutes]
  rw[mul_add_distributes]
  rw[mul_one]
  rw[mul_commutes]
  rw[mul_add_distributes]
  rw[mul_add_distributes]
  rw[mul_one]

-- def Rational (x: ℝ) := ∃ (p q : Nat), x = p/q

-- def Irrational (x: ℝ) := x ∉ Rational

-- we want to eventually prove that root 2 is irrational

end MyNat
