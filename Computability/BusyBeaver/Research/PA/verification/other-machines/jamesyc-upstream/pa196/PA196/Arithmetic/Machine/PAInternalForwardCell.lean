module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalScanRight
public import Mathlib.Tactic.Ring.Basic
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.ForwardCell
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem segment (n l t : V) : ∃ qs ls rs,
    Segment (n+2) qs ls rs 64 l (4*repeatBits n 1 t+2)
      64 (repeatBits n 1 (4*l+1)) t := by
  have r0 : row (⟨64,by decide⟩ : WorkingState) false =
      ⟨false,true,some ⟨0,by decide⟩⟩ := by rfl
  have r1 : row (⟨0,by decide⟩ : WorkingState) true =
      ⟨true,true,some ⟨64,by decide⟩⟩ := by rfl
  have self : row (⟨64,by decide⟩ : WorkingState) true =
      ⟨true,true,some ⟨64,by decide⟩⟩ := by rfl
  have a := right_row (⟨64,by decide⟩ : WorkingState) false (by rw [r0]) l
    ((1+1)*repeatBits n 1 t+1)
  rw [r0] at a
  simp only [StepFormula.controlCode,Bool.toNat_true,Bool.toNat_false,
    Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,add_zero] at a
  have b := right_row (⟨0,by decide⟩ : WorkingState) true (by rw [r1])
    ((1+1)*l) (repeatBits n 1 t)
  rw [r1] at b
  simp only [StepFormula.controlCode,Bool.toNat_true,Bool.toNat_false,
    Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,add_zero] at b
  obtain ⟨qs,ls,rs,h⟩ := ScanRight.segment (⟨64,by decide⟩ : WorkingState)
    true true self n ((1+1)*((1+1)*l)+1) t
  simp only [Bool.toNat_true,Nat.cast_one] at h
  have joined := segment_prepend a (segment_prepend b h)
  have hl : (1+1)*((1+1)*l)+1=4*l+1 := by ring1
  have hi : (1+1)*((1+1)*repeatBits n 1 t+1)=4*repeatBits n 1 t+2 := by ring1
  have result : ∃ qs ls rs,
      Segment (n+1+1) qs ls rs 64 l ((1+1)*((1+1)*repeatBits n 1 t+1))
        64 (repeatBits n 1 ((1+1)*((1+1)*l)+1)) t := ⟨_,_,_,joined⟩
  simpa only [hl,hi,show n+1+1=n+2 by ring1] using result
end Models

def sentence : ArithmeticSentence :=
  “∀ n l t, ∃ r l', !repeatGraph r n 1 t ∧ !repeatGraph l' n 1 (4*l+1) ∧
    ∃ qs ls rs, !segmentFormula (n+2) qs ls rs 64 l (4*r+2) 64 l' t”
theorem pa_proves_forward_cell : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [repeat_defined.df,segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_forward_cell
end PA196.Arithmetic.Machine.PA.InternalTrace.ForwardCell

