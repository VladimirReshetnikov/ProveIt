import DirectMainForward

/-! Converse only on the image condition G>w. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainRestricted
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph DirectMainForward
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def inverse (v : Fin 12 → V) : Fin 12 → V := Function.update v 11 (v 11-v 5)

theorem inverse_positive (v : Fin 12 → V) (hv : ∀j,0<v j) (hgap : v 5<v 11) :
    ∀j, 0 < inverse v j := by
  intro j
  by_cases h : j=11
  · subst j
    simpa [inverse] using tsub_pos_iff_lt.mpr hgap
  · simpa [inverse,h] using hv j

theorem inverse_transform (v : Fin 12 → V) (hgap : v 5<v 11) :
    transform (inverse v)=v := by
  funext j
  by_cases h : j=11
  · subst j
    simp only [transform,Function.update_self]
    have hi5 : inverse v 5=v 5 := by simp [inverse]
    have hi11 : inverse v 11=v 11-v 5 := by simp [inverse]
    rw [hi5,hi11,tsub_add_cancel_of_le (le_of_lt hgap)]
  · simp [transform,inverse,h]

theorem transform_gap (v : Fin 12 → V) (hv : ∀j,0<v j) :
    transform v 5<transform v 11 := by
  have h : v 5<v 11+v 5 := lt_add_of_pos_left _ (hv 11)
  simpa [transform] using h

theorem exists_iff_restricted (p : Fin 4 → ℕ) :
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJXQ91.graph (integerPorts p)).output v) ↔
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ v 5<v 11 ∧ InternalZero (graph (integerPorts p)).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ⟨transform v,transform_pos v hv,transform_gap v hv,(zero_iff p v).mpr hz⟩
  · rintro ⟨v,hv,hgap,hz⟩
    refine ⟨inverse v,inverse_positive v hv hgap,?_⟩
    apply (zero_iff p (inverse v)).mp
    rw [inverse_transform v hgap]
    exact hz

#print axioms DirectMainRestricted.exists_iff_restricted
end DirectMainRestricted
