import Absorb89Forward

/-! Reverse the forward map when the absorbed witness exceeds s. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89Inverse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89Forward
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def inverse (v : Fin 12 → V) : Fin 12 → V := Function.update v 7 (v 7-v 6)

theorem inverse_pos (v : Fin 12 → V) (hv : ∀j,0<v j) (h : v 6<v 7) : ∀j,0<inverse v j := by
  intro j
  by_cases hj : j=7
  · subst j
    simpa [inverse] using tsub_pos_iff_lt.mpr h
  · simpa [inverse,hj] using hv j

theorem transform_inverse (v : Fin 12 → V) (h : v 6≤v 7) : transform (inverse v)=v := by
  funext i
  by_cases hi : i=7
  · subst i
    simp [transform,inverse,tsub_add_cancel_of_le h]
  · simp [transform,inverse,hi]

theorem exists_direct_of_gap (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hv : ∀j,0<v j) (hgap : v 6<v 7)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃w : Fin 12 → V, (∀j,0<w j) ∧
      InternalZero (FreeJDirectMainGraph.graph (integerPorts p)).output w := by
  refine ⟨inverse v,inverse_pos v hv hgap,?_⟩
  apply (Absorb89Forward.zero_iff p (inverse v)).mp
  rw [transform_inverse v (le_of_lt hgap)]
  exact hz

#print axioms Absorb89Inverse.transform_inverse
#print axioms Absorb89Inverse.exists_direct_of_gap
end Absorb89Inverse
