import Surreal.Surcomplex.ConditionedCosineValuation
import Surreal.Surcomplex.TrigonometricLeading

/-!
# Failure of the equality threshold for inverse cosine

For every positive surreal exponent `κ`, an actual positive infinitesimal
angle has sine valuation `κ` and endpoint defect of valuation `2κ`.
Adding that defect reaches the endpoint; adding twice the defect removes
all real finite-angle solutions. This proves the strict-threshold clause
of `trigonometry:thm:conditioned`.
-/

universe u

namespace Surreal.Surcomplex.ConditionedCosine

open Foundations

noncomputable section

local notation "v" => SignSequence.valuation

/-- At every positive scale, equality in the conditioning bound can reach the critical
endpoint or take the target outside the range of every real finite-angle cosine. -/
theorem exists_threshold_counterexample (k : SignSequence.{u}) (hk : 0 < k) :
    ∃ (θ : SignSequence.FiniteElement.{u}) (e : SignSequence.{u}),
      θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) ∧
      SignSequence.IsInfinitesimal θ.val ∧
      v (finiteSin θ) = ↑k ∧ 0 < e ∧ SignSequence.IsInfinitesimal e ∧
      v e = ↑(2 * k) ∧ v (2 * e) = ↑(2 * k) ∧
      finiteCos θ + e = 1 ∧ 1 < finiteCos θ + 2 * e ∧
      ∀ φ : SignSequence.FiniteElement.{u}, finiteCos φ ≠ finiteCos θ + 2 * e := by
  have hi : SignSequence.IsInfinitesimal (SignSequence.tMonomial k) := by
    rw [SignSequence.isInfinitesimal_iff_valuation_pos, SignSequence.valuation_tMonomial]
    exact WithTop.coe_pos.mpr hk
  let θ : SignSequence.FiniteElement.{u} :=
    ⟨SignSequence.tMonomial k, SignSequence.finite_of_infinitesimal hi⟩
  have hθp : 0 < θ.val := SignSequence.tMonomial_pos k
  have hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) := by
    refine ⟨hθp, ?_⟩
    have h := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt θ.val).mp hi
      Real.pi Real.pi_pos
    rwa [abs_of_pos hθp] at h
  have hsin : v (finiteSin θ) = ↑k :=
    (valuation_finiteSin_of_isInfinitesimal θ hi).trans (SignSequence.valuation_tMonomial k)
  have hc := CirclePerturbation.coordinate_mem_Ioo (finiteCos θ) (finiteSin θ)
    (finiteSin_pos_of_mem_Ioo θ hθ) (finiteCos_sq_add_finiteSin_sq θ)
  let e := 1 - finiteCos θ
  have hep : 0 < e := sub_pos.mpr hc.2
  have he : v e = ↑(2 * k) := by
    rw [valuation_one_sub_finiteCos_of_isInfinitesimal θ hi]
    change 2 • v (SignSequence.tMonomial k) = _
    rw [SignSequence.valuation_tMonomial, two_nsmul, ← WithTop.coe_add, ← two_mul]
  have hei : SignSequence.IsInfinitesimal e := by
    rw [SignSequence.isInfinitesimal_iff_valuation_pos, he]
    exact WithTop.coe_pos.mpr (mul_pos (by norm_num) hk)
  have htwo : v (2 : SignSequence.{u}) = 0 := by
    simpa only [map_ofNat] using
      (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0))
  have he2 : v (2 * e) = ↑(2 * k) := by
    rw [SignSequence.valuation_mul, htwo, he, zero_add]
  have hend : finiteCos θ + e = 1 := by dsimp only [e]; ring
  have hout : 1 < finiteCos θ + 2 * e := by linarith only [hend, hep]
  refine ⟨θ, e, hθ, hi, hsin, hep, hei, he, he2, hend, hout, ?_⟩
  intro φ hφ
  have hb := (finiteCos_mem_Icc φ).2
  rw [hφ] at hb
  exact (not_le_of_gt hout) hb

end
end Surreal.Surcomplex.ConditionedCosine
