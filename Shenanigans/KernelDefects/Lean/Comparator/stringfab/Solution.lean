/-
Same fabrication, with an empty `Type` field instead of a `Prop` field, so the
compiler needs no erasure internals and the module declares NO axioms at all.
-/
prelude

inductive False : Prop

inductive Empty : Type

-- The only way to build a `String` is from an inhabitant of `Empty`.  Nobody
-- can -- except the kernel, when it meets a string literal.
inductive String : Type where
  | ofList : Empty -> String

/-- `Q s` unfolds to `False` for any string the kernel can expand. -/
noncomputable def Q (s : String) : Prop :=
  @String.rec (fun _ => Prop) (fun _ => False) s

/-- Entirely legitimate: `String.ofList` carries an `Empty`, so eliminate it.
    Vacuous in any honest environment. -/
theorem extract (s : String) : Q s :=
  @String.rec (fun s => Q s) (fun e => @Empty.rec (fun _ => False) e) s

/-- The kernel expands `"a"` into
    `String.ofList (List.cons (Char.ofNat 97) List.nil)`, fabricating an
    inhabitant of `Empty`. -/
theorem boom : False := extract "a"

#print axioms boom

theorem anything (P : Prop) : P := @False.rec (fun _ => P) boom

#print axioms anything

set_option genCtorIdx false in
inductive Nat : Type where | zero : Nat | succ : Nat -> Nat
def Nat.add (_ _ : Nat) : Nat := Nat.zero

-- stubs so lean4export can produce a "primitive-complete" export
set_option genCtorIdx false in
inductive Bool : Type where | false : Bool | true : Bool
def Nat.sub (_ _ : Nat) : Nat := Nat.zero
def Nat.mul (_ _ : Nat) : Nat := Nat.zero
def Nat.pow (_ _ : Nat) : Nat := Nat.zero
def Nat.gcd (_ _ : Nat) : Nat := Nat.zero
def Nat.div (_ _ : Nat) : Nat := Nat.zero
def Nat.mod (_ _ : Nat) : Nat := Nat.zero
def Nat.beq (_ _ : Nat) : Bool := Bool.false
def Nat.ble (_ _ : Nat) : Bool := Bool.false
def Nat.land (_ _ : Nat) : Nat := Nat.zero
def Nat.lor (_ _ : Nat) : Nat := Nat.zero
def Nat.xor (_ _ : Nat) : Nat := Nat.zero
def Nat.shiftLeft (_ _ : Nat) : Nat := Nat.zero
def Nat.shiftRight (_ _ : Nat) : Nat := Nat.zero
