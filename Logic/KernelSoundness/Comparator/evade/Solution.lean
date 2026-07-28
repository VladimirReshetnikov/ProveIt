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

/-- `Q ""` is `True`; `Q "a"` is `False`. -/
noncomputable def Q (s : String) : Prop :=
  @String.rec (fun _ => Prop)
    (fun l => @List.rec Char (fun _ => Prop) True (fun _ _ _ => False) l) s

/-- Legitimate: a non-empty `List Char` yields `False`, because a `Char` carries
    an `Empty`.  Vacuous in any honest environment -- nobody can build a `Char`. -/
theorem extract (s : String) : Q s :=
  @String.rec (fun s => Q s)
    (fun l => @List.rec Char (fun l => Q (String.ofList l))
                True.intro
                (fun c _ _ => @Char.rec (fun _ => False)
                                (fun e => @Empty.rec (fun _ => False) e) c)
                l)
    s

/-- The kernel expands `"a"` into
    `String.ofList (List.cons (Char.ofNat 97) List.nil)`, fabricating a `Char`
    -- and hence an `Empty` -- out of the numeral 97. -/
theorem boom : False := extract "a"

#print axioms boom
