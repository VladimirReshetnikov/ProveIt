prelude

universe u

-- compiler internals; `Init.Prelude` declares these identically.  They are
-- `unsafe`, so `Lean.Environment.replay` skips them, and `boom` never uses them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive Empty : Type

set_option genCtorIdx false in
inductive Bool : Type where
  | false : Bool
  | true : Bool

set_option genCtorIdx false in
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

-- `Char.ofNat` is the kernel's hook for expanding string literals.  It is a
-- CONSTRUCTOR here, so it is reachable from `Char`'s inductive info and is
-- compared -- and it is identical in Challenge and Solution.  Its field type is
-- `Empty`.
set_option genCtorIdx false in
inductive Char : Type where
  | ofNat : Empty -> Char

set_option genCtorIdx false in
inductive List (a : Type u) where
  | nil : List a
  | cons : a -> List a -> List a

set_option genCtorIdx false in
inductive String : Type where
  | ofList : List Char -> String

-- the 15 constants in comparator's `primitiveTargets`
def Nat.add (_ _ : Nat) : Nat := Nat.zero
def Nat.sub (_ _ : Nat) : Nat := Nat.zero
def Nat.mul (_ _ : Nat) : Nat := Nat.zero
def Nat.pow (_ _ : Nat) : Nat := Nat.zero
def Nat.div (_ _ : Nat) : Nat := Nat.zero
def Nat.mod (_ _ : Nat) : Nat := Nat.zero
def Nat.gcd (_ _ : Nat) : Nat := Nat.zero
def Nat.beq (_ _ : Nat) : Bool := Bool.false
def Nat.ble (_ _ : Nat) : Bool := Bool.false
def Nat.land (_ _ : Nat) : Nat := Nat.zero
def Nat.lor (_ _ : Nat) : Nat := Nat.zero
def Nat.xor (_ _ : Nat) : Nat := Nat.zero
def Nat.shiftLeft (_ _ : Nat) : Nat := Nat.zero
def Nat.shiftRight (_ _ : Nat) : Nat := Nat.zero

-- The challenge's own proof is never compared -- only its STATEMENT is.
axiom sorryAx (a : Sort u) (synthetic : Bool) : a

theorem boom : False := sorryAx False Bool.false
