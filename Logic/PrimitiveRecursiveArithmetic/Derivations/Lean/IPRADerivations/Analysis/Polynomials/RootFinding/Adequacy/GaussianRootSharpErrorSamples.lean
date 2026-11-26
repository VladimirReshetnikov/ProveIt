import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerEnvelope
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerRadiusPerturbation
import IPRADerivations.Analysis.Polynomials.Evaluation.GaussianPolynomialValueName
import IPRADerivations.Analysis.Names.Approximation.GaussianRepresentedPointBounds

/-!
# Sharp C_Z polynomial-error constant with explicit finite sample slack

The actual sampled query is only known to lie in the rational disk
Z+2^(-s). Exact rational-radius Horner perturbation and a proved finite
power envelope retain the source constant C_Z=N Z^(N-1), placing all
remaining sample error in a computed K·2^(-s). No disk rounding replaces
the target constant by C_(Z+1). All numerical inputs are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSharpErrorSamples

open_ipra
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (coefficientConstant)
open LeanProofs.IPRA.Analysis.GaussianRepresentedPointBounds (normLE norm_le_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cost (N Z : PTm n) : PTm n :=
  N*(two*GaussianRationalPowerEnvelope.error Z (pred N)+pw (Z+one) (pred N))
def observation (step a : PR 3) (point : PR 2) (N t x s : PTm n) : PTm n :=
  qsub (evaluate (GaussianRootRadius.product step a N t x) (ap2 point s x))
    (GaussianPolynomialValueName.observation a point N x s)

ipra_subst cost
ipra_subst observation

theorem coarse_power (Z H r : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le (pw (Z*H+one) r) (pw (Z+one) r*pw H r) := by
  have h : Γ ⊢[PRAAx] le (Z*H+one) ((Z+one)*H) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_refl (Z*H)) hH)
  exact le_congr (.eqRefl _) (GaussianProductStability.power_product _ _ _)
    (pw_le_pw r h)

/-- The actual rational-disk coefficient estimate has sharp main term
2 C_Z/D and a computed sample slack cost/H, uniformly in D>=1. -/
theorem error_budget (N Z H D : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    le (N*pw (Z*H+one) (pred N)*(two*H+D))
      ((two*coefficientConstant N Z*H+cost N Z*D)*pw H (pred N)) := by
  let K := GaussianRationalPowerEnvelope.error Z (pred N)
  let U := pw (Z+one) (pred N)
  let V := pw H (pred N)
  have first := mul_le_mul_right (two*N) (GaussianRationalPowerEnvelope.power_envelope_cross Z H (pred N) hH)
  have second := mul_le_mul_right (N*D) (coarse_power Z H (pred N) hH)
  have firstTwo : Γ ⊢[PRAAx] le (N*pw (Z*H+one) (pred N)*(two*H+D))
      ((two*coefficientConstant N Z*H+two*N*K+N*U*D)*V) :=
    le_congr (by ipra_ring) (by unfold coefficientConstant; ipra_ring) (add_le_add₂ first second)
  have enlarge : Γ ⊢[PRAAx] le (two*N*K) (two*N*K*D) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (two*N*K)) hD)
  have total := add_le_add₂ (add_le_add₂ (le_refl (two*coefficientConstant N Z*H)) enlarge) (le_refl (N*U*D))
  exact le_trans firstTwo (le_congr (.eqRefl _) (by unfold cost; ipra_ring) (mul_le_mul_right V total))

theorem observation_bound (step a : PR 3) (point : PR 2) (N Z t x s : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hZ : Γ ⊢[PRAAx] le one Z)
    (hNorm : Γ ⊢[PRAAx] normLE point Z x) : Γ ⊢[PRAAx]
    bounded (observation step a point N t x s)
      (two*coefficientConstant N Z*unit s+cost N Z*GaussianRootFiniteEvaluation.denominator a N t x)
      (GaussianRootFiniteEvaluation.denominator a N t x*unit s) := by
  let H := unit s
  let D := GaussianRootFiniteEvaluation.denominator a N t x
  have hp : Γ ⊢[PRAAx] le one H := unit_positive s
  have dp : Γ ⊢[PRAAx] le one D := GaussianRootFiniteEvaluation.denominator_positive a N t x
  have dhp := positive_product _ _ dp hp
  have radiusOrder : Γ ⊢[PRAAx] le H (Z*H+one) :=
    le_trans (le_congr (one_mul _) (.eqRefl _) (le_mul_mono hZ (le_refl H))) (le_add_right _ one)
  have actual := GaussianRationalHornerRadiusPerturbation.evaluation_bound
    (GaussianRootRadius.product step a N t x) (GaussianRootSamples.sample a N s x) (ap2 point s x)
    N (Z*H+one) H (two*H+D) (D*H)
    (GaussianRootRadius.product_length step a N t x) (GaussianRootSamples.sample_length a N s x)
    ((GaussianRootRadius.product_leading step a N t x).eqTrans (GaussianRootSamples.sample_leading a N s x).eqSymm)
    hp radiusOrder dhp (GaussianRootFiniteEvaluation.coefficient_errors step a N t s x hRD hCN hN)
    (norm_le_at point Z x s hNorm)
  have budget : Γ ⊢[PRAAx] le ((N*pw (Z*H+one) (pred N)*(two*H+D))*(D*H))
      ((two*coefficientConstant N Z*H+cost N Z*D)*(pw H (pred N)*(D*H))) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (D*H) (error_budget N Z H D hp dp))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (GaussianPolynomialPerturbation.power_positive _ _ hp) dhp) dhp budget actual

theorem sharp_sample_error_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶
      le (var 0*pw (var 1*var 2+one) (pred (var 0))*(two*var 2+var 3))
        ((two*coefficientConstant (var 0) (var 1)*var 2+cost (var 0) (var 1)*var 3)*pw (var 2) (pred (var 0)))) :=
  closeUniv 4 (.impI (.impI (error_budget _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem sharp_sample_error_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le one (var 1) ⟶ normLE point (var 1) (var 3) ⟶
      bounded (observation step a point (var 0) (var 2) (var 3) (var 4))
        (two*coefficientConstant (var 0) (var 1)*unit (var 4)+cost (var 0) (var 1)*GaussianRootFiniteEvaluation.denominator a (var 0) (var 2) (var 3))
        (GaussianRootFiniteEvaluation.denominator a (var 0) (var 2) (var 3)*unit (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI
    (observation_bound _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianRootSharpErrorSamples
