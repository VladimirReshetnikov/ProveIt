import PositiveMap86To87
import ModelMap87To86

/-! Source-only positive model comparison; all transitive imports are
unelaborated, and no endpoint or provider closure is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelEquivalence8687Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive-zero equivalence with the reverse calibration's
explicit Mersenne, port, size, and mask hypotheses. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta K MC MF t : V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMCcast : (p 2 : DiffRing V)=ι MC) (hMFcast : (p 3 : DiffRing V)=ι MF)
    (hMC : MC<beta) (hMF : MF<2*beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P86ResidueGraph.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P87ShiftedGuard.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact PositiveMap86To87Draft.positive_map p beta K v hport hK hv hz
  · rintro ⟨v,hv,hz⟩
    exact ModelMap87To86Draft.positive_map p beta K MC MF t v hbeta hbeta46 ht hradix
      hport hK hMCcast hMFcast hMC hMF hv hz

end DiophantineConsistency.ModelEquivalence8687Draft

#print axioms DiophantineConsistency.ModelEquivalence8687Draft.positive_zero_iff
