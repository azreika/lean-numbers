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


def Nat.one : Nat := (Nat.succ Nat.zero)
def Nat.two : Nat := (Nat.succ Nat.one)
def Nat.three : Nat := Nat.two.succ
def Nat.four : Nat := Nat.three.succ


end MyNat
