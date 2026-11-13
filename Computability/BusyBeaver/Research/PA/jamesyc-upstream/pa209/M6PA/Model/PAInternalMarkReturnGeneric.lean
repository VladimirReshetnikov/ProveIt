module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalLeftPhase
public import Mathlib.Tactic.Ring.Basic
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace.MarkReturnGeneric
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem segment (q : WorkingState)
    (r0 : row q true=⟨true,false,some ⟨3,by decide⟩⟩) (n l t : V) : ∃ qs ls rs,
    Phase (n+2) qs ls rs q.val (repeatBits n 1 (4*l+1)) t
      4 l (4*repeatBits n 1 t+2) := by
  have r1 : row (⟨3,by decide⟩ : WorkingState) false =
      ⟨false,false,some ⟨4,by decide⟩⟩ := by rfl
  have first := LeftPhase.left_row_any q true
    (by rw [r0]) (repeatBits n 1 (2*l)) t
  rw [r0] at first
  simp only [StepFormula.controlCode,Bool.toNat_true,Nat.cast_one,Nat.cast_ofNat] at first
  obtain ⟨qs,ls,rs,hs⟩ := LeftPhase.segment (⟨3,by decide⟩ : WorkingState)
    true true (by rfl) n (2*l) ((1+1)*t+1)
  simp only [Bool.toNat_true,Nat.cast_one] at hs
  have hd : (2*l)/2=l := by simpa [one_add_one_eq_two] using LeftPhase.bit_div false l
  have hm : (2*l)%2=0 := by simpa [one_add_one_eq_two] using LeftPhase.bit_mod false l
  rw [hd,hm] at hs
  simp only [add_zero] at hs
  have last := LeftPhase.left_row_any (⟨3,by decide⟩ : WorkingState) false
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

#print axioms segment
end M6.Arithmetic.PA.InternalTrace.MarkReturnGeneric

