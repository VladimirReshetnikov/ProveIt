import OmegaGtF87
import ConditionalMap87To88

/-! Source-only calibrated 87→88 positive map. No Lean elaboration,
provider closure, parent endpoint or file binding is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMap87To88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive map using the same 87 zero for the strict guard
calibration. No Mersenne or q|X hypothesis is used. -/
theorem positive_map (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P88QuotientGuarded.graph p).output v' := by
  have hstrict : v 1<v 13 := OmegaGtF87Draft.omega_gt_F p beta K MC MF v
    hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  exact ConditionalMap87To88Draft.positive_map p v hv hstrict hz

end DiophantineConsistency.ModelMap87To88Draft

#print axioms DiophantineConsistency.ModelMap87To88Draft.positive_map
