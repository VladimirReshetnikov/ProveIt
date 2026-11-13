import Absorb88Conditional
import Absorb89Transport

/-! Exact positive-zero equivalence for the transport-restricted 88 graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb88Restricted
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_iff (p : Fin 4 → ℕ) (hb : 0<(p 0:V)) :
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v ∧
      (v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5)) ↔
    (∃w : Fin 12 → V, (∀j,0<w j) ∧ InternalZero (FreeJAbsorb89.graph (integerPorts p)).output w) := by
  constructor
  · exact Absorb88Conditional.exists_89_of_transport p hb
  · rintro ⟨v,hv,hz⟩
    refine ⟨Absorb88Forward.transform p v,Absorb88Forward.transform_pos p v hv,
      (Absorb88Forward.zero_iff p v).mpr hz,?_⟩
    simpa [Absorb88Forward.transform] using (Absorb89Transport.transport p v hb hv hz).1

#print axioms Absorb88Restricted.positive_zero_iff
end Absorb88Restricted
