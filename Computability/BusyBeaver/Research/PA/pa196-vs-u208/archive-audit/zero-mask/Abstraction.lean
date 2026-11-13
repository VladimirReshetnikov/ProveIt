import M6.Source.Semantics

/-! A conditional Boolean-mask invariant for the actual M6 source semantics.
The closure assumptions are not yet connected to the archived bitset checks. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PA196ZeroMask
open M6.Source

abbrev Mask := Fin 9 → Bool

def mask (registers : Registers) : Mask := fun i => decide (registers i > 0)

def setMask (m : Mask) (r : Fin 9) (b : Bool) : Mask :=
  fun i => if i = r then b else m i

/-- Nine-bit natural-number encoding used as an index into an archive bitset. -/
def encode (m : Mask) : Nat :=
  (if m 0 then 2^0 else 0) ||| (if m 1 then 2^1 else 0) |||
  (if m 2 then 2^2 else 0) ||| (if m 3 then 2^3 else 0) |||
  (if m 4 then 2^4 else 0) ||| (if m 5 then 2^5 else 0) |||
  (if m 6 then 2^6 else 0) ||| (if m 7 then 2^7 else 0) |||
  (if m 8 then 2^8 else 0)

private theorem ite_testBit (b : Bool) (x k : Nat) :
    (if b then x else 0).testBit k = (b && x.testBit k) := by
  cases b <;> simp

theorem encode_testBit (m : Mask) (r : Fin 9) : (encode m).testBit r = m r := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [encode, Nat.testBit_or, ite_testBit, Nat.testBit_two_pow]
  all_goals try simp only [show ((3 : Fin 9) : Nat) = 3 from rfl,
    show ((4 : Fin 9) : Nat) = 4 from rfl, show ((5 : Fin 9) : Nat) = 5 from rfl,
    show ((6 : Fin 9) : Nat) = 6 from rfl, show ((7 : Fin 9) : Nat) = 7 from rfl,
    show ((8 : Fin 9) : Nat) = 8 from rfl, decide_true, decide_false, Bool.and_true,
    Bool.and_false, Bool.or_false, Bool.false_or]
  all_goals simp

theorem encode_bound (m : Mask) : encode m < 512 := by
  change encode m < 2^9
  unfold encode
  repeat first | apply Nat.or_lt_two_pow | (split <;> decide)

@[simp] theorem mask_apply (registers : Registers) (r : Fin 9) :
    mask registers r = decide (registers r > 0) := rfl

@[simp] theorem mask_write_inc (registers : Registers) (r : Fin 9) :
    mask (write registers r (registers r + 1)) = setMask (mask registers) r true := by
  funext i
  by_cases h : i = r
  · subst i
    simp [mask, write, setMask]
  · simp [mask, write, setMask, h]

@[simp] theorem mask_write_dec (registers : Registers) (r : Fin 9) :
    mask (write registers r (registers r - 1)) =
      setMask (mask registers) r (decide (registers r - 1 > 0)) := by
  funext i
  by_cases h : i = r
  · subst i
    simp [mask, write, setMask]
  · simp [mask, write, setMask, h]

/-- Abstract closure for every resolved instruction and every recorded mask.
The positive decrement permits either resulting bit, as in the finite certificate. -/
structure Closed (sites : Array Site) (allowed : Nat → Mask → Prop) : Prop where
  inc : ∀ pc m r target, resolveAt sites pc = some (.inc r (some target)) →
    allowed pc m → allowed target (setMask m r true)
  dec_zero : ∀ pc m r target positive, resolveAt sites pc = some (.dec r (some target) positive) →
    allowed pc m → m r = false → allowed target m
  dec_positive : ∀ pc m r zero target b, resolveAt sites pc = some (.dec r zero (some target)) →
    allowed pc m → m r = true → allowed target (setMask m r b)
  jump : ∀ pc m target, resolveAt sites pc = some (.jump (some target)) →
    allowed pc m → allowed target m

/-- Terminal and malformed controls are harmless for this invariant. -/
def Holds (allowed : Nat → Mask → Prop) (c : Configuration) : Prop :=
  match c.control with
  | .at pc => allowed pc (mask c.registers)
  | _ => True

theorem step_preserves (sites : Array Site) (allowed : Nat → Mask → Prop)
    (closed : Closed sites allowed) (c : Configuration) (hc : Holds allowed c) :
    Holds allowed (step sites c) := by
  cases c with
  | mk control registers =>
    cases control with
    | exited | halted | malformed => simp [step, Holds]
    | «at» pc =>
      simp only [Holds] at hc
      simp only [step]
      cases hr : resolveAt sites pc with
      | none => simp [Holds]
      | some op =>
        cases op with
        | inc r next =>
          cases next with
          | none => simp [execute, destination, Holds]
          | some target =>
            simpa [execute, destination, Holds] using closed.inc pc (mask registers) r target hr hc
        | dec r zero positive =>
          by_cases hz : registers r = 0
          · cases zero with
            | none => simp [execute, destination, Holds, hz]
            | some target =>
              have hb : mask registers r = false := by simp [mask, hz]
              simpa [execute, destination, Holds, hz] using
                closed.dec_zero pc (mask registers) r target positive hr hc hb
          · cases positive with
            | none => simp [execute, destination, Holds, hz]
            | some target =>
              have hb : mask registers r = true := by simp [mask, Nat.pos_of_ne_zero hz]
              simpa [execute, destination, Holds, hz] using
                closed.dec_positive pc (mask registers) r zero target
                  (decide (registers r - 1 > 0)) hr hc hb
        | jump next =>
          cases next with
          | none => simp [execute, destination, Holds]
          | some target =>
            simpa [execute, destination, Holds] using closed.jump pc (mask registers) target hr hc
        | halt => simp [execute, Holds]

theorem steps_preserve (sites : Array Site) (allowed : Nat → Mask → Prop)
    (closed : Closed sites allowed) {n : Nat} {a b : Configuration}
    (run : Steps sites n a b) (ha : Holds allowed a) : Holds allowed b := by
  induction run with
  | refl => exact ha
  | cons tail ih => exact ih (step_preserves sites allowed closed _ ha)

#print axioms mask_write_inc
#print axioms mask_write_dec
#print axioms encode_testBit
#print axioms encode_bound
#print axioms step_preserves
#print axioms steps_preserve
end PA196ZeroMask
