import DiophantineConsistency.Compact44.Absorb89Inverse
import DiophantineConsistency.Compact44.Absorb89Select

/-! Positive-zero existence equivalence at bounded ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89Equivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89Forward
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_iff (p : Fin 4 → ℕ)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V)) :
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v) ↔
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJDirectMainGraph.graph (integerPorts p)).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    obtain ⟨w,hw,hgap,hwz⟩ := Absorb89Select.select p v hb hl hh hv hz
    exact Absorb89Inverse.exists_direct_of_gap p w hw hgap hwz
  · exact Absorb89Forward.exists_absorb_of_direct p

#print axioms Absorb89Equivalence.positive_zero_iff
end Absorb89Equivalence
