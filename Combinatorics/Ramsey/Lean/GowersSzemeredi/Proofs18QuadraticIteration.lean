import GowersSzemeredi.Proofs18DensityIteration
import GowersSzemeredi.Proofs18QuadraticIterationStep

/-! Complete finite iteration for the four-term case, with an explicit
recursive length threshold and no inverse-theorem hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticIntervalIterationThreshold (delta : Real) : Real :=
  densityIterationThreshold (intervalQuadraticStepThreshold delta)
    (intervalQuadraticLengthFactor delta) (intervalQuadraticLengthExponent delta)
    ⌈(intervalQuadraticGain delta)⁻¹⌉₊

/-- The explicit quadratic increment terminates after at most ceil(1/gain)
steps. This is a full interval theorem; no qualitative Szemeredi input or
conditional higher-degree theorem is assumed. -/
theorem quadratic_interval_szemeredi_recursive
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (L : Nat) (hL : quadraticIntervalIterationThreshold delta ≤ L)
    (B : Finset (Fin L)) (hcard : delta * L ≤ B.card) : HasNatAP (B.image Fin.val) 4 := by
  obtain ⟨hg, hρ, hc⟩ := intervalQuadratic_constants_pos hδ
  have hsteps : (intervalQuadraticGain delta)⁻¹ ≤ (⌈(intervalQuadraticGain delta)⁻¹⌉₊ : Real) :=
    Nat.le_ceil _
  have hm := mul_le_mul_of_nonneg_right hsteps hg.le
  rw [inv_mul_cancel₀ hg.ne'] at hm
  exact hasNatAP_of_density_iteration hg.le hc hρ
    (interval_quadratic_iteration_step delta hδ hδone) _ L hL B delta le_rfl hcard (by linarith)

end LeanProofs.GowersSzemeredi
