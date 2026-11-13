import PositiveMap88To87
import ModelMap87To88

/-! Source-only positive model comparison. All transitive imports remain
unelaborated, with provider and endpoint obligations open. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelEquivalence8788Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive-zero equivalence, retaining reverse calibration's
explicit beta size, port casts and mask bounds. No Mersenne hypothesis. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta K MC MF : V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P87ShiftedGuard.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P88QuotientGuarded.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ModelMap87To88Draft.positive_map p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  · rintro ⟨v,hv,hz⟩
    exact PositiveMap88To87Draft.positive_map p v hv hz

end DiophantineConsistency.ModelEquivalence8788Draft

#print axioms DiophantineConsistency.ModelEquivalence8788Draft.positive_zero_iff
