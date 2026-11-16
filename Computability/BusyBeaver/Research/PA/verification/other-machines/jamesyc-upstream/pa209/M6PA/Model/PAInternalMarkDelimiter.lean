module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalLeftPhase
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.MarkDelimiter
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem segment (l t : V) : ∃ qs ls rs,
    Segment 3 qs ls rs 51 l (4*t+2) 2 (l/2) ((1+1)*(4*t)+l%2) := by
  have r0 : row (⟨51,by decide⟩ : WorkingState) false =
      ⟨false,true,some ⟨17,by decide⟩⟩ := by rfl
  have r1 : row (⟨17,by decide⟩ : WorkingState) true =
      ⟨false,false,some ⟨2,by decide⟩⟩ := by rfl
  have r2 : row (⟨2,by decide⟩ : WorkingState) false =
      ⟨false,false,some ⟨2,by decide⟩⟩ := by rfl
  have a := right_row (⟨51,by decide⟩ : WorkingState) false (by rw [r0]) l ((1+1)*t+1)
  rw [r0] at a
  simp only [StepFormula.controlCode,Bool.toNat_false,Nat.cast_zero,add_zero] at a
  have b := left_row (⟨17,by decide⟩ : WorkingState) true false (by rw [r1]) l t
  rw [r1] at b
  simp only [StepFormula.controlCode,Bool.toNat_true,Bool.toNat_false,Nat.cast_zero,Nat.cast_one,add_zero] at b
  have c := LeftPhase.left_row_any (⟨2,by decide⟩ : WorkingState) false (by rw [r2]) l ((1+1)*t)
  rw [r2] at c
  simp only [StepFormula.controlCode,Bool.toNat_false,Nat.cast_zero,add_zero] at c
  have h := segment_prepend a (segment_prepend b (segment_one c))
  have hi : (1+1)*((1+1)*t+1)=4*t+2 := by ring1
  have ho : (1+1)*((1+1)*((1+1)*t))+l%2=(1+1)*(4*t)+l%2 := by ring1
  have result : ∃ qs ls rs, Segment 3 qs ls rs 51 l ((1+1)*((1+1)*t+1))
      2 (l/2) ((1+1)*((1+1)*((1+1)*t))+l%2) := ⟨_,_,_,by simpa only [Nat.cast_ofNat,show (1 : V)+1+1=3 by ring1] using h⟩
  simpa only [hi,ho] using result
end Models

def sentence : ArithmeticSentence :=
  “∀ l t, ∃ a b, !divDef a l 2 ∧ !remDef b l 2 ∧
    ∃ qs ls rs, !segmentFormula 3 qs ls rs 51 l (4*t+2) 2 a ((1+1)*(4*t)+b)”
theorem pa_proves_mark_delimiter : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [div_defined.df,rem_defined.df,segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_mark_delimiter
end M6.Arithmetic.PA.InternalTrace.MarkDelimiter

