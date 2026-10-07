import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def polarizationPhase : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

noncomputable def polarizationWeight (k : Fin 4) : ℂ := polarizationPhase k / 4

theorem polarizationPhase_norm (k : Fin 4) : ‖polarizationPhase k‖ = 1 := by
  fin_cases k <;> norm_num [polarizationPhase]

theorem polarizationWeight_norm (k : Fin 4) : ‖polarizationWeight k‖ = (1 : ℝ) / 4 := by
  simp only [polarizationWeight, norm_div, polarizationPhase_norm]
  norm_num

theorem polarizationWeight_cost : (∑ k, ‖polarizationWeight k‖) = 1 := by
  simp only [polarizationWeight_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem complex_mixed_polarization (a b c d : ℂ) :
    a * star d = ∑ k, polarizationWeight k *
      ((a + polarizationPhase k * b) * star (c + polarizationPhase k * d)) := by
  norm_num [Fin.sum_univ_succ, polarizationWeight, polarizationPhase,
    star_add, star_mul, Complex.star_def]
  ring_nf
  norm_num [Complex.I_sq]
  ring

end Erdos3

end

end OAI
