
import Project1.Integers.Integers
import Project1.Integers.Arithmetic
import Project1.Integers.Inequalities

namespace MyInt

def Set (a : Type) := a -> Prop
instance { a : Type } : Membership a (Set a) where
  mem s x := s x

def LinearCombinations (a b : Int) : Set Int :=
  fun x => ∃ m n : Int, x = a * m + b * n

def PosLinearCombinations ( a b : Int ) : Set Int :=
  fun x => (x ∈ (LinearCombinations a b) ∧ .zero < x)

def is_min (x : Int) (s: Set Int) : Prop :=
  x ∈ s ∧ (
    ∀ (y : Int), (y ∈ s → x ≤ y)
  )

def has_min (s : Set Int) : Prop :=
  ∃ (m : Int), is_min m s

def is_nonempty (s : Set Int) : Prop :=
  ∃ (x : Int), x ∈ s

theorem lte_neq_succ (m n : Nat) (h1 : m ≤ n.succ) (h2 : m ≠ n.succ) :
  m ≤ n :=
  by
    induction m generalizing n with
    | zero =>
      exact MyNat.gte_zero n
    | succ m ih =>
      cases n with
      | zero =>
        apply Classical.byContradiction
        intro h3
        have h4 : (m ≤ MyNat.Nat.zero) := h1
        have h5 := MyNat.gte_zero m
        have h6 := MyNat.lte_antisym m MyNat.Nat.zero h4 h5
        rw[h6] at h2
        contradiction
      | succ n =>
        change m ≤ n
        have h3 : m ≤ n.succ := h1
        have h4 : (m  ≠ n.succ) := by
          apply Classical.byContradiction
          intro h4
          simp at h4
          rw[h4] at h2
          simp at h2
        have ih2 := ih n h3 h4
        exact ih2

theorem pos_nonempty_lemma1 (s : Set Int) (n : Nat) (h1: ∃ (m : Nat), (m ≤ n) ∧ (intOfNat m) ∈ s) (h2 : ∀ (x : Int), (x ∈ s → .zero ≤ x)) :
  has_min s :=
    by
      induction n with
      | zero =>
        unfold has_min
        exists .zero
        unfold is_min
        constructor
        obtain ⟨ m, hm ⟩ := h1
        have hm1 := hm.left
        have hm2 := hm.right
        have hm3 : (m = .zero) :=
          by
            have hx := MyNat.gte_zero m
            have hx2 := MyNat.lte_antisym m MyNat.Nat.zero hm1 hx
            exact hx2
        rw[hm3] at hm2
        rw[<-Int.zero] at hm2
        exact hm2
        intro y
        intro h3
        have h4 := h2 y  h3
        exact h4
      | succ n ih =>
        unfold has_min
        obtain ⟨ m, hm ⟩ := h1
        have hm1 := hm.left
        have hm2 := hm.right
        unfold is_min
        by_cases hy : (∃ (m : Nat), m ≤ n ∧ intOfNat m ∈ s)
        have hh := ih hy
        exact hh

        simp at hy
        exists intOfNat n.succ
        constructor
        apply Classical.byContradiction
        intro hz
        by_cases hx : m = n.succ
        rw[hx] at hm2
        contradiction

        have hx2 : m ≤ n := lte_neq_succ m n hm1 hx
        have hy2 := hy m hx2
        contradiction

        intro yy
        intro hy3

        apply Classical.byContradiction
        intro hy4

        by_cases hx3 : yy < .zero
        have hh2 := h2 yy hy3
        have hx4 := lt_means_lte yy Int.zero hx3
        have hx5 := lte_antisym yy Int.zero hx4 hh2
        have hx6 := lt_means_neq yy Int.zero hx3
        contradiction

        have hx4 := not_lt_means_flip_lte yy Int.zero hx3

        have hy5 := not_lte_means_flip_lt (intOfNat n.succ) yy hy4
        have hx5 := nonneg_is_nat yy hx4
        obtain ⟨ k, hk ⟩ := hx5
        rw[hk] at hy5
        have hx6 := intofnat_lt_equiv_rev k n.succ hy5
        have hx7 : (k ≤ n) := by
          dsimp [MyNat.Nat.lt] at hx6
          exact lte_neq_succ k n hx6.left hx6.right
        have hx8 := hy k hx7
        rw[<-hk] at hx8
        contradiction

theorem pos_nonempty_has_min (s : Set Int) (h1: is_nonempty s) (h2 : ∀ (x : Int), (x ∈ s → .zero ≤ x)) :
  has_min s :=
  by
    unfold is_nonempty at h1
    obtain ⟨ m, m_in_s ⟩ := h1
    have m_geq_zero := h2 m m_in_s
    have m_nat := nonneg_is_nat m m_geq_zero
    obtain ⟨ k, hk ⟩ := m_nat
    have exists_k : ( ∃ (m : Nat), (m ≤ k) ∧ (intOfNat m) ∈ s) :=
      by
        exists k
        constructor
        exact MyNat.leq_itself k
        rw[hk] at m_in_s
        exact m_in_s
    exact pos_nonempty_lemma1 s k exists_k h2

theorem expand_poscom_set ( x a b : Int ) :
  (x ∈ PosLinearCombinations a b) ↔ (∃ (m n : Int), x = a * m + b * n) ∧ .zero < x :=
  by
    constructor

    intro h1
    simp only [(· ∈ · )] at h1
    unfold PosLinearCombinations at h1
    unfold LinearCombinations at h1
    simp only [(· ∈ · )] at h1
    exact h1

    intro h1
    simp only [(· ∈ · )]
    unfold PosLinearCombinations
    unfold LinearCombinations
    simp only [(· ∈ · )]
    exact h1

end MyInt
