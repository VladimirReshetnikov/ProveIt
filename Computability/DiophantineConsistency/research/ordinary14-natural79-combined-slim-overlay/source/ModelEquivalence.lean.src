import ModelMap
import ModelMap85To84

/-! Source-only positive 84↔85 model equivalence under explicit symbolic
hypotheses. Both imported directions and all dependencies are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelEquivalence8485Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed all-positive model-zero equivalence; explicit beta size,
Mersenne, mask and natural port-cast hypotheses apply in both directions. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta K MC MF t : V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMCcast : (p 2 : DiffRing V)=ι MC) (hMFcast : (p 3 : DiffRing V)=ι MF)
    (hMC : MC<beta) (hMF : MF<2*beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P84QcubeGraph.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P85QcubeGraph.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ModelMap84To85Draft.positive_map p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  · rintro ⟨v,hv,hz⟩
    exact ModelMap85To84Draft.positive_map p beta K MC MF t v hbeta hbeta46 ht hradix
      hport hK hMCcast hMFcast hMC hMF hv hz

end DiophantineConsistency.ModelEquivalence8485Draft

#print axioms DiophantineConsistency.ModelEquivalence8485Draft.positive_zero_iff
