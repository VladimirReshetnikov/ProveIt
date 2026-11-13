module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalTracePrepend
public import M6PA.Model.PAInternalTraceRows
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.IncrementTail
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
private def push (b : Bool) (x : V) : V := (1+1)*x+b.toNat

private lemma step0 (l : V) : Step 1 l (0 : V) 91 (push true l) (0 : V) := by
  have hr : row (⟨1,by decide⟩ : WorkingState) false = ⟨true,true,some ⟨91,by decide⟩⟩ := by rfl
  have h := right_row (⟨1,by decide⟩ : WorkingState) false (by rw [hr]) (l : V) 0
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

private lemma step1 (l : V) : Step 91 (push true l) (0 : V) 66 (push false (push true l)) (0 : V) := by
  have hr : row (⟨91,by decide⟩ : WorkingState) false = ⟨false,true,some ⟨66,by decide⟩⟩ := by rfl
  have h := right_row (⟨91,by decide⟩ : WorkingState) false (by rw [hr]) ((push true l) : V) 0
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

private lemma step2 (l : V) : Step 66 (push false (push true l)) (0 : V) 180 (push true (push false (push true l))) (0 : V) := by
  have hr : row (⟨66,by decide⟩ : WorkingState) false = ⟨true,true,some ⟨180,by decide⟩⟩ := by rfl
  have h := right_row (⟨66,by decide⟩ : WorkingState) false (by rw [hr]) ((push false (push true l)) : V) 0
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

private lemma step3 (l : V) : Step 180 (push true (push false (push true l))) (0 : V) 40 (push false (push true l)) (push true (push true (0 : V))) := by
  have hr : row (⟨180,by decide⟩ : WorkingState) false = ⟨true,false,some ⟨40,by decide⟩⟩ := by rfl
  have h := left_row (⟨180,by decide⟩ : WorkingState) false true (by rw [hr]) ((push false (push true l)) : V) (0 : V)
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

private lemma step4 (l : V) : Step 40 (push false (push true l)) (push true (push true (0 : V))) 54 (push true l) (push false (push true (push true (0 : V)))) := by
  have hr : row (⟨40,by decide⟩ : WorkingState) true = ⟨true,false,some ⟨54,by decide⟩⟩ := by rfl
  have h := left_row (⟨40,by decide⟩ : WorkingState) true false (by rw [hr]) ((push true l) : V) (push true (0 : V))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

private lemma step5 (l : V) : Step 54 (push true l) (push false (push true (push true (0 : V)))) 40 l (push true (push false (push true (push true (0 : V))))) := by
  have hr : row (⟨54,by decide⟩ : WorkingState) false = ⟨false,false,some ⟨40,by decide⟩⟩ := by rfl
  have h := left_row (⟨54,by decide⟩ : WorkingState) false true (by rw [hr]) (l : V) (push true (push true (0 : V)))
  rw [hr] at h
  simpa [push,StepFormula.controlCode] using h

theorem segment (l : V) : ∃ qs ls rs, Segment 6 qs ls rs 1 l 0 40 l 13 := by
  have h6 := segment_zero (40 : V) l (push true (push false (push true (push true (0 : V)))))
  have h5 := segment_prepend_nat (n := 0) (step5 l) h6
  have h4 := segment_prepend_nat (n := 1) (step4 l) h5
  have h3 := segment_prepend_nat (n := 2) (step3 l) h4
  have h2 := segment_prepend_nat (n := 3) (step2 l) h3
  have h1 := segment_prepend_nat (n := 4) (step1 l) h2
  have h0 := segment_prepend_nat (n := 5) (step0 l) h1
  have result : ∃ qs ls rs, Segment 6 qs ls rs 1 l 0 40 l (push true (push false (push true (push true (0 : V))))) := ⟨_,_,_,h0⟩
  have he : (push true (push false (push true (push true (0 : V)))))=(13 : V) := by simp only [push,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero]; ring1
  simpa only [he] using result
end Models

def sentence : ArithmeticSentence :=
  “∀ l, ∃ qs ls rs, !segmentFormula 6 qs ls rs 1 l 0 40 l 13”
theorem pa_proves_append_one_tail : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_append_one_tail
end M6.Arithmetic.PA.InternalTrace.IncrementTail

