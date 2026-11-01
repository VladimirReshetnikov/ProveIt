import DiophantineConsistency.AdaptiveDirectOrdinate86Residue
import DiophantineConsistency.AdaptiveDirectOrdinate86AuxNormClient

/-! Actual 86-positive zero yields a positive-shifted 87 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Forward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairs
open AdaptiveFirstRootFactor87Syntax ArithmeticPellHalfIndex
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Witness
open AdaptiveDirectOrdinate86Residue AdaptiveDirectOrdinate86AuxNormClient
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_positive_zero_to_old_natural86 (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀i : Fin 13,0<v (embed i))
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) (fun i => v (embed i))) :
    ∃ w : Fin 13 → V, InternalZero
      (positiveShift (AdaptiveFirstRootFactor87Literal.expressionAt87 (fun j => (p j:ℤ)))) w := by
  let q : V := 1+v 0*(p 0:V)
  let c : V := v 9+v 7*(v 9+v 10)
  let I : V := (c*c)*v 4
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have h := expressionAt_signed_residue86 p (fun i => v (embed i)) hb hl hh hv hz
  have hn := actual_norm_for_witness (fun j => (p j:ℤ)) v hz
  have hm := congrArg magnitude (signedV_eval (fun j => (p j:ℤ)) v)
  rw [hm] at h
  change 2≤v 4*c*c ∧ 2≤R ∧ 2*R<c ∧ SignMod c (magnitude (splitEval (signedV (fun j => (p j:ℤ))) v)) R at h
  have hI : 2≤I := by simpa only [I,mul_comm,mul_left_comm,mul_assoc] using h.1
  exact new_positive_zero_to_old_natural_of_norm_residue (fun j => (p j:ℤ)) v I c R hv hI h.2.1 h.2.2.1 h.2.2.2 hn hz
end DiophantineConsistency.AdaptiveDirectOrdinate86Forward
