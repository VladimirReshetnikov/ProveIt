import PowerRecovery87
import MersenneGuard87
import ConditionalMap87To86

/-! Source-only proposed direct 87→86 positive map. All transitive clients
remain unelaborated; no provider or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMap87To86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive 87 zero maps to an 86 zero under explicit Mersenne, natural
port and mask hypotheses. The power and projection are from that 87 zero. -/
theorem positive_map (p : Fin 4 → ℤ) (beta K MC MF t : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMCcast : (p 2 : DiffRing V)=ι MC) (hMFcast : (p 3 : DiffRing V)=ι MF)
    (hMC : MC<beta) (hMF : MF<2*beta) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P86ResidueGraph.graph p).output v' := by
  let R := naturalRank beta MC MF v
  have hX : v 6=Exp.exp R := by
    simpa only [R,MainBalance87Draft.X] using
      PowerRecovery87Draft.power p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  have h3 : PositiveMap86To87Draft.q beta v∣3*v 6 := by
    simpa only [PositiveMap86To87Draft.q,FirstFields86Draft.q,MainBalance87Draft.X] using
      Divides3X87Draft.divides_three_X p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have hstrict : PositiveMap86To87Draft.C beta v*K<v 13 :=
    MersenneGuard87Draft.strict_of_power p beta K t R v hbeta ht hradix hport hK hv hX h3 hz
  have hgap : v 1+v 2<PositiveMap86To87Draft.q beta v := by
    simpa only [PositiveMap86To87Draft.q,AuxGraphNormClientDraft.q] using
      GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz
  exact ConditionalMap87To86Draft.positive_map p beta K v hport hK hv hgap hstrict hz

end DiophantineConsistency.ModelMap87To86Draft

#print axioms DiophantineConsistency.ModelMap87To86Draft.positive_map
