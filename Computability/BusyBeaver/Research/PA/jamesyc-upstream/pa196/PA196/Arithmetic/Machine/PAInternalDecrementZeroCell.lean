module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalLeftPhase
public import PA196.Arithmetic.Machine.PAInternalTracePrepend
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.DecrementZeroCell
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
private def push (b : Bool) (x : V) : V := (1+1)*x+b.toNat
private lemma step0 (l t : V) : Step 1 l (push false (push false (push false (push true t)))) 91 (push true l) (push false (push false (push true t))) := by
  have hr : row (⟨1,by decide⟩ : WorkingState) false = ⟨true,true,some ⟨91,by decide⟩⟩ := by rfl
  have h := right_row (⟨1,by decide⟩ : WorkingState) false (by rw [hr]) l (push false (push false (push true t)))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step1 (l t : V) : Step 91 (push true l) (push false (push false (push true t))) 66 (push false (push true l)) (push false (push true t)) := by
  have hr : row (⟨91,by decide⟩ : WorkingState) false = ⟨false,true,some ⟨66,by decide⟩⟩ := by rfl
  have h := right_row (⟨91,by decide⟩ : WorkingState) false (by rw [hr]) (push true l) (push false (push true t))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step2 (l t : V) : Step 66 (push false (push true l)) (push false (push true t)) 180 (push true (push false (push true l))) (push true t) := by
  have hr : row (⟨66,by decide⟩ : WorkingState) false = ⟨true,true,some ⟨180,by decide⟩⟩ := by rfl
  have h := right_row (⟨66,by decide⟩ : WorkingState) false (by rw [hr]) (push false (push true l)) (push true t)
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step3 (l t : V) : Step 180 (push true (push false (push true l))) (push true t) 109 (push false (push true l)) (push true (push true t)) := by
  have hr : row (⟨180,by decide⟩ : WorkingState) true = ⟨true,false,some ⟨109,by decide⟩⟩ := by rfl
  have h := left_row (⟨180,by decide⟩ : WorkingState) true true (by rw [hr]) (push false (push true l)) t
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step4 (l t : V) : Step 109 (push false (push true l)) (push true (push true t)) 94 (push true l) (push false (push false (push true t))) := by
  have hr : row (⟨109,by decide⟩ : WorkingState) true = ⟨false,false,some ⟨94,by decide⟩⟩ := by rfl
  have h := left_row (⟨109,by decide⟩ : WorkingState) true false (by rw [hr]) (push true l) (push true t)
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step5 (l t : V) : Step 94 (push true l) (push false (push false (push true t))) 109 l (push true (push true (push false (push true t)))) := by
  have hr : row (⟨94,by decide⟩ : WorkingState) false = ⟨true,false,some ⟨109,by decide⟩⟩ := by rfl
  have h := left_row (⟨94,by decide⟩ : WorkingState) false true (by rw [hr]) l (push false (push true t))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step6 (l t : V) : Step 109 l (push true (push true (push false (push true t)))) 94 (l/2)
    ((1+1)*(push false (push true (push false (push true t))))+l%2) := by
  have hr : row (⟨109,by decide⟩ : WorkingState) true = ⟨false,false,some ⟨94,by decide⟩⟩ := by rfl
  have h := LeftPhase.left_row_any (⟨109,by decide⟩ : WorkingState) true (by rw [hr]) l (push true (push false (push true t)))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

/-- Zero-decrement delimiter with a nonempty following cell; no standardness
assumption on the arbitrary residual suffix. The endpoint is left-headed. -/
theorem segment (l t : V) : ∃ qs ls rs,
    Segment 7 qs ls rs 1 l (16*t+8) 94 (l/2) (2*(16*t+10)+l%2) := by
  have h7 := segment_zero (94 : V) (l/2) ((1+1)*(push false (push true (push false (push true t))))+l%2)
  have h6 := segment_prepend_nat (n := 0) (step6 l t) h7
  have h5 := segment_prepend_nat (n := 1) (step5 l t) h6
  have h4 := segment_prepend_nat (n := 2) (step4 l t) h5
  have h3 := segment_prepend_nat (n := 3) (step3 l t) h4
  have h2 := segment_prepend_nat (n := 4) (step2 l t) h3
  have h1 := segment_prepend_nat (n := 5) (step1 l t) h2
  have h0 := segment_prepend_nat (n := 6) (step0 l t) h1
  have hi : push false (push false (push false (push true t))) = 16*t+8 := by
    simp only [push,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero]; ring1
  have ho : (1+1)*(push false (push true (push false (push true t))))+l%2 = 2*(16*t+10)+l%2 := by
    simp only [push,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero]; ring1
  exact ⟨_,_,_, by simpa only [hi,ho,Nat.reduceAdd,Nat.cast_ofNat] using h0⟩
end Models

def sentence : ArithmeticSentence :=
  “∀ l t, ∃ a b, !divDef a l 2 ∧ !remDef b l 2 ∧
    ∃ qs ls rs, !segmentFormula 7 qs ls rs 1 l (16*t+8) 94 a (2*(16*t+10)+b)”
theorem pa_proves_zero_delimiter : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [div_defined.df,rem_defined.df,segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_zero_delimiter
end PA196.Arithmetic.Machine.PA.InternalTrace.DecrementZeroCell

