import DiophantineConsistency.AdaptiveDirectOrdinate86Rank
import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011

/-! Actual 86-zero early-index residue and index comparison. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Comparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveEarlyIndex2011 ArithmeticAdaptiveIndexComparison2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86MainOrientation
open AdaptiveDirectOrdinate86Indices AdaptiveDirectOrdinate86Rank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem expressionAt_early_index86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : EarlyIndex p v := by
  have hp := scaled_parameters_positive p v hb hv
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient86 p v hb hv hz
  have hs' : v 7=(1+v 0*(p 0:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  exact early_index_of_facts p v (lt_trans (by simp : (0:V)<1) hp.1) hv ⟨s,hs'⟩
    (expressionAt_indices86 p v hb hv hz) (expressionAt_rank_window86 p v hb hl hh hv hz)
    (expressionAt_rank_congruence86 p v hb hv hz)

theorem expressionAt_comparison86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : Comparison p v := by
  have hY : 2≤v 7 := two_le_of_positive_cube_quotient
    (scaled_parameters_positive p v hb hv).1 (expressionAt_Y_quotient86 p v hb hv hz)
  exact comparison_of_facts p v hv hY (expressionAt_indices86 p v hb hv hz)
    (expressionAt_early_index86 p v hb hl hh hv hz)

end DiophantineConsistency.AdaptiveDirectOrdinate86Comparison
