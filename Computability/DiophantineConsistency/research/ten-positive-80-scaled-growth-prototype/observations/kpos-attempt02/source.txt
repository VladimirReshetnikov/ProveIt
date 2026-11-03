import Direct80CAboveX

/-! The signed Kpos factor has a positive gap for every actual graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80Kpos
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open TenPositive80Graph TenPositive80Factors Direct80CAboveX
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_positive_gap (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    2*X p v<3*c p v ∧ 0<3*c p v-2*X p v := by
  have h := graph_c_above_x p v hb hv hz
  have h2 : 2*X p v<2*c p v := mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : 2*c p v≤3*c p v := mul_le_mul_of_nonneg_right (by norm_num : (2:V)≤3) (by simp)
  have hgap := lt_of_lt_of_le h2 h3
  exact ⟨hgap,tsub_pos_iff_lt.mpr hgap⟩

#print axioms Direct80Kpos.graph_positive_gap
end Direct80Kpos
