import DirectMainGap
import DirectMainRestricted

/-! Positive-zero equivalence for bounded arbitrary ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_iff (p : Fin 4 → ℕ)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V)) :
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (DirectMainForward.integerPorts p)).output v) ↔
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJXQ91.graph (DirectMainForward.integerPorts p)).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    have hgap : v 5<v 11 := DirectMainGap.graph_gap p v hb hl hh hv hz
    exact (DirectMainRestricted.exists_iff_restricted p).mpr ⟨v,hv,hgap,hz⟩
  · intro h
    exact DirectMainForward.exists_direct_of_xq91 p h

#print axioms DirectMainEquivalence.positive_zero_iff
end DirectMainEquivalence
