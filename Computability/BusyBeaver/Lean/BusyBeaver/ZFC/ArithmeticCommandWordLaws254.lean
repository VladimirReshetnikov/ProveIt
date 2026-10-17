import BusyBeaver.ZFC.ArithmeticCommandAppend254

/-!
Algebraic laws for represented command words at all internal model inputs.
The shifted empty word is 0. Tail replacement acts on a raw command, before
adding the shifted-word marker. These are word laws, not execution contracts.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandWord254 ArithmeticCommandAppend254
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

section IOpen
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

@[simp] theorem first_replace (raw rest : V) :
    first (replaceValue raw rest) = first raw := by
  by_cases h : first raw < 3 <;> simp [replaceValue, h]

@[simp] theorem tail_replace (raw rest : V) :
    tailValue (replaceValue raw rest) = rest := by
  by_cases h : first raw < 3 <;> simp [tailValue, replaceValue, h]

@[simp] theorem replace_twice (raw left right : V) :
    replaceValue (replaceValue raw left) right = replaceValue raw right := by
  by_cases h : first raw < 3 <;> simp [replaceValue, h]

@[simp] theorem replace_own_tail (raw : V) :
    replaceValue raw (tailValue raw) = raw := by
  by_cases h : first raw < 3 <;> simp [replaceValue, tailValue, h]

end IOpen

section ISigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem append_right_zero (left : V) : appendValue left 0 = left := by
  induction left using ISigma1.sigma1_order_induction
  · definability
  case ind left ih =>
    rcases zero_or_succ left with (rfl | ⟨raw, rfl⟩)
    · simp
    · rw [appendValue_succ, ih (tailValue raw) (lt_succ_iff_le.mpr (tailValue_le raw)),
        replace_own_tail]

/-- Associativity uses Sigma1 induction with the other two inputs fixed.
It does not assume that an internal word is an external finite list. -/
theorem append_assoc (left middle right : V) :
    appendValue (appendValue left middle) right =
      appendValue left (appendValue middle right) := by
  induction left using ISigma1.sigma1_order_induction
  · definability
  case ind left ih =>
    rcases zero_or_succ left with (rfl | ⟨raw, rfl⟩)
    · simp
    · rw [appendValue_succ, appendValue_succ, tail_replace, replace_twice,
        appendValue_succ, ih (tailValue raw) (lt_succ_iff_le.mpr (tailValue_le raw))]

end ISigma1
end SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254
