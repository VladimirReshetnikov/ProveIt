import PowerRecovery85
import ModifiedCarrierFacts
import ConditionalComparison

/-! Source-only direct 85→84 positive map. All imported graph/calibration
sources are unelaborated; no 84 zero or q|X is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMap85To84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open NaturalRank84Draft ModifiedCarrierFactsDraft Conditional84To85Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed 85→84 positive map from the 85 graph's own zero, with explicit
Mersenne and size premises and no pre-assumed q|X. -/
theorem positive_map (p : Fin 4 → ℤ) (beta K MC MF t : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMCcast : (p 2 : DiffRing V)=ι MC) (hMFcast : (p 3 : DiffRing V)=ι MF)
    (hMC : MC<beta) (hMF : MF<2*beta) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P84QcubeGraph.graph p).output v' := by
  let qq := q beta v
  let R := naturalRank beta MC MF v
  have hX : v 6=Exp.exp R := by
    simpa only [DirectNorms85Draft.X,R] using
      PowerRecovery85Draft.power p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  have h3 : qq∣3*v 6 := by
    simpa only [qq,q,DirectNorms85Draft.q,DirectNorms85Draft.X] using
      Divides3X85Draft.divides_three_X p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have hq : qq=(Exp.exp t-1)*v 0+1 := by
    dsimp [qq,q]
    rw [hradix]
    ring
  have hd : qq∣v 6 := mersenne_divides_X t R qq (v 0) (v 6) ht hq hX h3
  exact map_85_to_84 p beta v hport hv hd hz

end DiophantineConsistency.ModelMap85To84Draft

#print axioms DiophantineConsistency.ModelMap85To84Draft.positive_map
