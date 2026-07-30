prelude
import Init.Prelude
import Init.Core

def Nat.gcd (a : Nat) (_b : Nat) : Nat := a

theorem gcd_left (a b : Nat) : Nat.gcd a b = a := rfl
theorem gcd_lit : Nat.gcd 0 1 = 1 := rfl

theorem zero_eq_one : (0 : Nat) = 1 :=
  @Eq.rec Nat (Nat.gcd 0 1) (fun x _ => x = 1) gcd_lit 0 (gcd_left 0 1)

theorem boom : False := Nat.noConfusion zero_eq_one

-- stubs so that lean4export can produce a "primitive-complete" export
def Nat.land (_ _ : Nat) : Nat := 0
def Nat.lor (_ _ : Nat) : Nat := 0
def Nat.xor (_ _ : Nat) : Nat := 0
def Nat.shiftRight (_ _ : Nat) : Nat := 0
def Nat.shiftLeft (_ _ : Nat) : Nat := 0
