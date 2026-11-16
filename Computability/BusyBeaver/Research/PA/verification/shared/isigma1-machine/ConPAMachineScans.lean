import ConPAMachineSegments
import BusyBeaver.ZFC.ArithmeticTapePrefix254

/-! A self-loop certified in a finite table scans an entire run of identical
bits, at lengths that may be nonstandard in an IΣ₁ model. -/

set_option autoImplicit false

namespace ConPA.Machine
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254

def findRow (T : Table) (q b : Nat) : Option Row :=
  T.find? fun row => decide (q = row.q ∧ b = row.b)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem step_of_row (T : Table) (q b : Nat) (l r : V) (row : Row)
    (hr : r % 2 = (b : V)) (hrow : findRow T q b = some row) :
    step T (⟪(q : V),l,r⟫ : V) = out row l r := by
  induction T with
  | nil => simp [findRow] at hrow
  | cons first tail ih =>
    by_cases h : q = first.q ∧ b = first.b
    · have he : first = row := by simpa [findRow, h] using hrow
      subst row
      simp [step, pi₁_pair, pi₂_pair, hr, h]
    · have ht : findRow tail q b = some row := by simpa [findRow, h] using hrow
      simpa [step, pi₁_pair, pi₂_pair, hr, h] using ih ht

/-- Prepend `n` copies of `bit` at the least-significant end of a tape half. -/
noncomputable def bitPrefix (bit : Bool) (n suffix : V) : V :=
  if bit then onesPrefix n suffix else Exp.exp n * suffix

private instance bitPrefix_delta (bit : Bool) : 𝚫₁-Function₂ (bitPrefix (V := V) bit) := by
  cases bit
  · change 𝚫₁-Function₂ (fun n suffix : V => Exp.exp n * suffix)
    definability
  · change 𝚫₁-Function₂ (onesPrefix (V := V))
    definability

@[simp] theorem bitPrefix_zero (bit : Bool) (suffix : V) : bitPrefix bit 0 suffix = suffix := by
  cases bit <;> simp [bitPrefix]

theorem bitPrefix_succ (bit : Bool) (n suffix : V) :
    bitPrefix bit (n + 1) suffix = 2 * bitPrefix bit n suffix + (bit.toNat : V) := by
  cases bit with
  | false => simp [bitPrefix, exp_succ, mul_assoc]
  | true => simpa [bitPrefix] using onesPrefix_succ n suffix

theorem bitPrefix_push (bit : Bool) (n suffix : V) :
    bitPrefix bit n (2 * suffix + (bit.toNat : V)) = bitPrefix bit (n + 1) suffix := by
  cases bit with
  | false => simp [bitPrefix, exp_succ]; ring
  | true => simpa [bitPrefix] using onesPrefix_push n suffix

/-- The near half includes the head. On a leftward scan place that bit back
in the ordinary right half of the packed configuration. -/
noncomputable def scanFrame (right : Bool) (q : Nat) (far near : V) : V :=
  if right then ⟪(q : V),far,near⟫ else ⟪(q : V),near / 2,2 * far + near % 2⟫

private instance scanFrame_delta (right : Bool) (q : Nat) : 𝚫₁-Function₂ (scanFrame (V := V) right q) := by
  cases right
  · change 𝚫₁-Function₂ (fun far near : V => ⟪(q : V),near / 2,2 * far + near % 2⟫)
    definability
  · change 𝚫₁-Function₂ (fun far near : V => ⟪(q : V),far,near⟫)
    definability

theorem scanStep (T : Table) (right b w : Bool) (q next : Nat) (far near : V)
    (hrow : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,right,next⟩) :
    step T (scanFrame right q far (2 * near + (b.toNat : V))) =
      scanFrame right next (2 * far + (w.toNat : V)) near := by
  have hb : (b.toNat : V) < 2 := by cases b <;> simp
  have div (x : V) : (2 * x + (b.toNat : V)) / 2 = x := div_mul_add' x 2 hb
  have rem (x : V) : (2 * x + (b.toNat : V)) % 2 = (b.toNat : V) := by
    rw [mul_comm 2 x]
    exact mod_mul_add_of_lt x 2 hb
  cases right with
  | false =>
    simp only [scanFrame, Bool.false_eq_true, if_false, div, rem]
    rw [step_of_row T q b.toNat near _ _ (rem far) hrow]
    simp only [out, Bool.false_eq_true, if_false, div]
    have he : 4 * far + 2 * (w.toNat : V) + near % 2 =
        2 * (2 * far + (w.toNat : V)) + near % 2 := by ring
    rw [he]
  | true =>
    simp only [scanFrame, if_true]
    rw [step_of_row T q b.toNat far _ _ (rem near) hrow]
    simp only [out, if_true, div]

/-- A certified table self-loop scans exactly `n` cells, rewriting the read
bit `b` to `w`. All tape halves and the clock belong to the model. -/
theorem scan (T : Table) (right b w : Bool) (q : Nat) (n far near : V)
    (hrow : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,right,q⟩) :
    runFrom T n (scanFrame right q far (bitPrefix b n near)) =
      scanFrame right q (bitPrefix w n far) near := by
  letI := runFrom_delta (V := V) T
  induction n using ISigma1.pi1_succ_induction generalizing far near with
  | hP => definability
  | zero => simp
  | succ n ih => rw [runFrom_first, bitPrefix_succ, scanStep _ _ _ _ _ _ _ _ hrow, ih, bitPrefix_push]

#print axioms step_of_row
#print axioms scan
end models
end ConPA.Machine
