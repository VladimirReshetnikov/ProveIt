prelude
import Init.Prelude

-- `Init.Prelude` does not define `Lean.reduceBool`; the kernel has nevertheless
-- already installed `reduce_native` for that name.  It is NOT in comparator's
-- `primitiveTargets` list either.
def Lean.reduceBool (_b : Bool) : Bool := true

def probe : Bool := false

theorem rb_decl (b : Bool) : Eq (Lean.reduceBool b) true := rfl
theorem rb_native : Eq (Lean.reduceBool probe) false := rfl

theorem true_eq_false : Eq true false :=
  @Eq.rec Bool (Lean.reduceBool probe) (fun x _ => Eq x false) rb_native true (rb_decl probe)

def IsTrue (b : Bool) : Prop := @Bool.rec (fun _ => Prop) False True b

theorem boom : False :=
  @Eq.rec Bool true (fun x _ => IsTrue x) True.intro false true_eq_false

-- stubs so lean4export can produce a "primitive-complete" export
def Nat.gcd (_ _ : Nat) : Nat := 0
def Nat.land (_ _ : Nat) : Nat := 0
def Nat.lor (_ _ : Nat) : Nat := 0
def Nat.xor (_ _ : Nat) : Nat := 0
def Nat.shiftRight (_ _ : Nat) : Nat := 0
def Nat.shiftLeft (_ _ : Nat) : Nat := 0
