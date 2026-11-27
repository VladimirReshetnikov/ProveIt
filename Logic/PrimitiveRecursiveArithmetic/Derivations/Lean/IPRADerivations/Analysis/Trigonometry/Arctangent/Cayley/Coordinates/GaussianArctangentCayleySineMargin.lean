import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.Coordinates.GaussianArctangentCayleyTrig
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameReciprocal

/-!
# Lower reciprocal margin for the literal Cayley sine

For 0 ≤ i ≤ M, the literal Cayley sine is at least i/M. The
comparison below is the exact norm-squared predicate used by the
reciprocal and residual bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleySineMargin

open_ipra
open ComplexLogarithmRemainder (normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (denominator denominator_positive)
open GaussianArctangentCayleyTrig (sinePoint sineCode)
open GaussianNameReciprocal (lower)
open GaussianRationalHorner (positive_product ofGaussian_represents)
open GaussianRationalMetric (qnormSq_represents squared_tolerance_represents comparison_of_cleared)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem lower_of_grid_margin (M i T : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hT : Γ ⊢[PRAAx] le one T)
    (hi : Γ ⊢[PRAAx] le i M) (h : Γ ⊢[PRAAx] le M (T*i)) :
    Γ ⊢[PRAAx] lower (sinePoint M i) T := by
  let N := two*M*i
  let E := denominator M i
  have hE := denominator_positive M i hM
  have cap : Γ ⊢[PRAAx] le E (two*(M*M)) :=
    le_congr (add_comm _ _) (by ipra_ring) (add_le_add_right (M*M) (le_mul_mono hi hi))
  have ray : Γ ⊢[PRAAx] le E (T*N) :=
    le_trans cap (le_congr (by ipra_ring) (by dsimp only [N]; ipra_ring) (le_mul_mono (le_refl (two*M)) h))
  have eq : Γ ⊢[PRAAx] normSq (sineCode M i) ≐ N*N := by
    apply deriveNat
    rw [normSq_eval]
    simp only [sineCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    dsimp only [N]
    ipra_simps
    ring
  have norm := qnormSq_represents _ _ _ hE (ofGaussian_represents (sineCode M i) E hE)
  exact comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hT hT) (positive_product _ _ hE hE)
    (squared_tolerance_represents one T hT) norm
    (le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] (T*N)*(T*N) ≐ (N*N)*(T*T)).eqTrans
      (congrMul eq.eqSymm (.eqRefl _))) (le_mul_mono ray ray))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleySineMargin
