module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalTracePrepend
public import PA196.Arithmetic.Machine.PAInternalTraceRows
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.DecrementPositiveCell
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
private def push (b : Bool) (x : V) : V := (1+1)*x+b.toNat
private lemma step0 (l t : V) :
    Step 1 l (push false (push false (push true t))) 91 (push true l) (push false (push true t)) := by
  have hr : row (⟨1,by decide⟩ : WorkingState) false = ⟨true,true,some ⟨91,by decide⟩⟩ := by rfl
  have h := right_row (⟨1,by decide⟩ : WorkingState) false (by rw [hr]) l (push false (push true t))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step1 (l t : V) :
    Step 91 (push true l) (push false (push true t)) 66 (push false (push true l)) (push true t) := by
  have hr : row (⟨91,by decide⟩ : WorkingState) false = ⟨false,true,some ⟨66,by decide⟩⟩ := by rfl
  have h := right_row (⟨91,by decide⟩ : WorkingState) false (by rw [hr]) (push true l) (push true t)
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step2 (l t : V) :
    Step 66 (push false (push true l)) (push true t) 54 (push true l) (push false (push true t)) := by
  have hr : row (⟨66,by decide⟩ : WorkingState) true = ⟨true,false,some ⟨54,by decide⟩⟩ := by rfl
  have h := left_row (⟨66,by decide⟩ : WorkingState) true false (by rw [hr]) (push true l) t
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
private lemma step3 (l t : V) :
    Step 54 (push true l) (push false (push true t)) 40 l (push true (push false (push true t))) := by
  have hr : row (⟨54,by decide⟩ : WorkingState) false = ⟨false,false,some ⟨40,by decide⟩⟩ := by rfl
  have h := left_row (⟨54,by decide⟩ : WorkingState) false true (by rw [hr]) l (push true t)
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h
/-- Positive-decrement delimiter, with an arbitrary model-valued residual suffix. -/
theorem segment (l t : V) : ∃ qs ls rs, Segment 4 qs ls rs 1 l (8*t+4) 40 l (8*t+5) := by
  have h4 := segment_zero (40 : V) l (push true (push false (push true t)))
  have h3 := segment_prepend_nat (n := 0) (step3 l t) h4
  have h2 := segment_prepend_nat (n := 1) (step2 l t) h3
  have h1 := segment_prepend_nat (n := 2) (step1 l t) h2
  have h0 := segment_prepend_nat (n := 3) (step0 l t) h1
  have hi : push false (push false (push true t)) = 8*t+4 := by
    simp only [push,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero]; ring1
  have ho : push true (push false (push true t)) = 8*t+5 := by
    simp only [push,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero]; ring1
  exact ⟨_,_,_, by simpa only [hi,ho,Nat.reduceAdd,Nat.cast_ofNat] using h0⟩
end Models

def sentence : ArithmeticSentence :=
  “∀ l t, ∃ qs ls rs, !segmentFormula 4 qs ls rs 1 l (8*t+4) 40 l (8*t+5)”
theorem pa_proves_positive_delimiter : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_positive_delimiter
end PA196.Arithmetic.Machine.PA.InternalTrace.DecrementPositiveCell

