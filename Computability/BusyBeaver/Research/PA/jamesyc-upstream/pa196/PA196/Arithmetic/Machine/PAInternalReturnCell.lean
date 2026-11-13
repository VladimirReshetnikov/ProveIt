module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalLeftPhase
public import Mathlib.Tactic.Ring.Basic
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.ReturnCell
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem segment (n l t : V) : ∃ qs ls rs,
    Phase (n+2) qs ls rs 40 (repeatBits n 1 (4*l+1)) t
      40 l (4*repeatBits n 1 t+2) := by
  have r0 : row (⟨40,by decide⟩ : WorkingState) true =
      ⟨true,false,some ⟨54,by decide⟩⟩ := by rfl
  have r1 : row (⟨54,by decide⟩ : WorkingState) false =
      ⟨false,false,some ⟨40,by decide⟩⟩ := by rfl
  have first := LeftPhase.left_row_any (⟨40,by decide⟩ : WorkingState) true
    (by rw [r0]) (repeatBits n 1 (2*l)) t
  rw [r0] at first
  simp only [StepFormula.controlCode,Bool.toNat_true,Nat.cast_one,Nat.cast_ofNat] at first
  obtain ⟨qs,ls,rs,hs⟩ := LeftPhase.segment (⟨54,by decide⟩ : WorkingState)
    true true ScanLeft.dense54_row n (2*l) ((1+1)*t+1)
  simp only [Bool.toNat_true,Nat.cast_one] at hs
  have hd : (2*l)/2=l := by simpa [one_add_one_eq_two] using LeftPhase.bit_div false l
  have hm : (2*l)%2=0 := by simpa [one_add_one_eq_two] using LeftPhase.bit_mod false l
  rw [hd,hm] at hs
  simp only [add_zero] at hs
  have last := LeftPhase.left_row_any (⟨54,by decide⟩ : WorkingState) false
    (by rw [r1]) l (repeatBits n 1 ((1+1)*t+1))
  rw [r1] at last
  simp only [StepFormula.controlCode,Bool.toNat_false,Nat.cast_zero,Nat.cast_ofNat,add_zero] at last
  have joined := segment_compose (segment_prepend first hs) (segment_one last)
  have hc : repeatBits n 1 (4*l+1)=(1+1)*repeatBits n 1 (2*l)+1 := by
    rw [show 4*l+1=(1+1)*(2*l)+1 by ring1,repeat_commute]
  have hcd : repeatBits n 1 (4*l+1)/2=repeatBits n 1 (2*l) := by
    rw [hc]
    simpa using LeftPhase.bit_div true (repeatBits n 1 (2*l))
  have hcm : repeatBits n 1 (4*l+1)%2=1 := by
    rw [hc]
    simpa using LeftPhase.bit_mod true (repeatBits n 1 (2*l))
  have he : (1+1)*((1+1)*repeatBits n 1 ((1+1)*t+1))+l%2 =
      (1+1)*(4*repeatBits n 1 t+2)+l%2 := by
    rw [repeat_commute]
    ring1
  simpa only [Phase,hcd,hcm,he,Nat.cast_ofNat,show n+1+1=n+2 by ring1] using joined
end Models

def sentence : ArithmeticSentence :=
  “∀ n l t, ∃ a b, !repeatGraph a n 1 (4*l+1) ∧ !repeatGraph b n 1 t ∧
    ∃ qs ls rs, !phaseFormula (n+2) qs ls rs 40 a t 40 l (4*b+2)”
theorem pa_proves_return_cell : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [repeat_defined.df,phase_correct,numeral_eq_natCast]
  exact segment

#print axioms segment
#print axioms pa_proves_return_cell
end PA196.Arithmetic.Machine.PA.InternalTrace.ReturnCell

