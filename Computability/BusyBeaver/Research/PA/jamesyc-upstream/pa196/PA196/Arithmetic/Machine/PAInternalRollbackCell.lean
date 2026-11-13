module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalLeftPhase
public import Mathlib.Tactic.Ring.Basic
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.RollbackCell
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem segment (n l t : V) : ∃ qs ls rs,
    Phase (n+2) qs ls rs 94 (repeatBits n 1 (4*l+2)) t
      94 l (4*repeatBits n 1 t+2) := by
  obtain ⟨qs,ls,rs,hs⟩ := LeftPhase.segment (⟨94,by decide⟩ : WorkingState)
    true true ScanLeft.dense94_row n (4*l+2) t
  simp only [Bool.toNat_true,Nat.cast_one] at hs
  have he : 4*l+2=(1+1)*((1+1)*l+1)+0 := by ring1
  have hdiv : (4*l+2)/2=(1+1)*l+1 := by
    rw [he]
    simpa using LeftPhase.bit_div false ((1+1)*l+1)
  have hmod : (4*l+2)%2=0 := by
    rw [he]
    simpa using LeftPhase.bit_mod false ((1+1)*l+1)
  rw [hdiv,hmod] at hs
  simp only [add_zero] at hs
  have r0 : row (⟨94,by decide⟩ : WorkingState) false =
      ⟨true,false,some ⟨109,by decide⟩⟩ := by rfl
  have r1 : row (⟨109,by decide⟩ : WorkingState) true =
      ⟨false,false,some ⟨94,by decide⟩⟩ := by rfl
  have a := left_row (⟨94,by decide⟩ : WorkingState) false true
    (by rw [r0]) l (repeatBits n 1 t)
  rw [r0] at a
  simp only [StepFormula.controlCode,Bool.toNat_false,Bool.toNat_true,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero] at a
  have b := LeftPhase.left_row_any (⟨109,by decide⟩ : WorkingState) true
    (by rw [r1]) l ((1+1)*repeatBits n 1 t+1)
  rw [r1] at b
  simp only [StepFormula.controlCode,Bool.toNat_false,Bool.toNat_true,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero] at b
  have two := segment_prepend a (segment_one b)
  have joined := segment_compose hs two
  have hend : (1+1)*((1+1)*((1+1)*repeatBits n 1 t+1))+l%2 =
      (1+1)*(4*repeatBits n 1 t+2)+l%2 := by ring1
  rw [hend] at joined
  simpa only [Phase,one_add_one_eq_two,Nat.cast_ofNat] using joined
end Models

def sentence : ArithmeticSentence :=
  “∀ n l t, ∃ a b, !repeatGraph a n 1 (4*l+2) ∧ !repeatGraph b n 1 t ∧
    ∃ qs ls rs, !phaseFormula (n+2) qs ls rs 94 a t 94 l (4*b+2)”
theorem pa_proves_rollback_cell : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [repeat_defined.df,phase_correct,numeral_eq_natCast]
  exact segment

#print axioms segment
#print axioms pa_proves_rollback_cell
end PA196.Arithmetic.Machine.PA.InternalTrace.RollbackCell

