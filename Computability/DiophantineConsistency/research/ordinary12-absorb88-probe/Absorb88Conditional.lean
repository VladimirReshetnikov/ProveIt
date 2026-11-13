import Absorb88Select

/-! Existence transport, with an explicit 88-side transport hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb88Conditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_89_of_transport (p : Fin 4 → ℕ) (hb : 0<(p 0:V))
    (h : ∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v ∧
      (v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5)) :
    ∃w : Fin 12 → V, (∀j,0<w j) ∧ InternalZero (FreeJAbsorb89.graph (integerPorts p)).output w := by
  obtain ⟨v,hv,hz,hbound⟩ := h
  obtain ⟨w,hw,hgap,hwz⟩ := Absorb88Select.select p v hb hv hz hbound
  exact Absorb88Inverse.exists_89_of_gap p w hw hgap hwz

theorem exists_88_of_89 (p : Fin 4 → ℕ)
    (h : ∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJAbsorb89.graph (integerPorts p)).output v) :
    ∃w : Fin 12 → V, (∀j,0<w j) ∧ InternalZero (graph (integerPorts p)).output w := by
  obtain ⟨v,hv,hz⟩ := h
  exact ⟨Absorb88Forward.transform p v,Absorb88Forward.transform_pos p v hv,
    (Absorb88Forward.zero_iff p v).mpr hz⟩

#print axioms Absorb88Conditional.exists_89_of_transport
#print axioms Absorb88Conditional.exists_88_of_89
end Absorb88Conditional
