import PositiveMap88To87
import FirstQuotient87

/-! Source-only 88 own-zero first-Pell quotient and root via the concrete
87 guard shift. No parent graph zero, index calibration or Lean run. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstQuotient88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The explicit t↦t+F shift transports an 88 zero, without requiring the
whole valuation to be positive. -/
theorem forward_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    InternalZero (P87ShiftedGuard.graph p).output (PositiveMap88To87Draft.forward v) := by
  apply (internalZero_iff _ _).mpr
  have h := Ring88To87Draft.output_eval p (fun j => ι (v j))
  rw [←PositiveMap88To87Draft.cast_forward v] at h
  rw [h]
  exact (internalZero_iff _ _).mp hz

/-- The 88 own-zero first norm yields positive s,tau with Y=q³s and tau²=D;
no sign, main norm, parent zero or mask bounds are needed. -/
theorem quotient_and_root (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    ∃ s tau : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧ tau*tau=radicand v := by
  let u := PositiveMap88To87Draft.forward v
  have hJ' : 0<u 0 := by simpa [u,PositiveMap88To87Draft.forward] using hJ
  have hY' : 0<u 7 := by simpa [u,PositiveMap88To87Draft.forward] using hY
  have hz' : InternalZero (P87ShiftedGuard.graph p).output u := forward_zero p v hz
  have h := FirstQuotient87Draft.quotient_and_root p beta u hbeta hJ' hY' hport hz'
  simpa [u,PositiveMap88To87Draft.forward,Q,q,radicand,firstP,ell,k] using h

end DiophantineConsistency.FirstQuotient88Draft

#print axioms DiophantineConsistency.FirstQuotient88Draft.quotient_and_root
