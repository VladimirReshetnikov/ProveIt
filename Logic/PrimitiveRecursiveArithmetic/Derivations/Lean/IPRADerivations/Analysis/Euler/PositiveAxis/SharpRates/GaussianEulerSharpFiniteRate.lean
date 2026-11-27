import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpGridRate
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.SlackRemoval.GaussianRationalSlackRemoval

/-!
# Sharp finite Euler estimate for the original samplers

The low and middle panels contribute the literal coefficient C_R/N.
The contiguous tail contributes one D_R times the original decay
observation at N/4. An explicit finite precision removes the mesh and
auxiliary allowances. The two requested output observations and the
requested decay observation keep their own precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpFiniteRate

open_ipra
open GaussianBetaSharpFiniteBinding (fullBeta fullEuler)
open GaussianBetaSharpCofinalSchedule (source cutoff factor)
open GaussianBetaFiniteEulerAtCutoff (minimumCutoff minimumCells minimumPrecision)
open GaussianBetaFiniteEulerComparison (supportWidth)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator fixed_denominator_positive)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finitePoint (q z R B A N : PTm n) : PTm n := ap2 eulerF q (eulerData z R B A N)
def improperPoint (v z R B A : PTm n) : PTm n :=
  ap2 GaussianEulerImproperName.nameF v (GaussianEulerImproperName.data z R B A)
def numerator (q v q0 R N : PTm n) : PTm n :=
  GaussianEulerSharpResidualAssembly.boundNumerator
    (GaussianEulerSharpDegreeSchedule.coefficient R*fixedDenominator q0 N+fixedNumerator q0 R N*N)
    (N*fixedDenominator q0 N) (unit q) (unit v)
def denominator (q v q0 N : PTm n) : PTm n :=
  GaussianEulerSharpResidualAssembly.boundDenominator (N*fixedDenominator q0 N) (unit q) (unit v)

/-- Run the common grid schedule using the finite sampler's support comparison. -/
theorem cofinal_observations_of_finite_binding (t q v q0 z R B A N u : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaSharpNaturalDegreeSchedule.source z R B A N)
    (bind : ∀ p k K : PTm n,
      (Γ ⊢[PRAAx] le N (top k A R)) → (Γ ⊢[PRAAx] le one K) →
      (Γ ⊢[PRAAx] le (minimumCutoff t A) k) →
      (Γ ⊢[PRAAx] le (minimumCells t k z R B A N) (supportWidth (etaDen k A R) N*K)) →
      (Γ ⊢[PRAAx] le (minimumPrecision t k z R B A N (supportWidth (etaDen k A R) N*K)) p) →
      (Γ ⊢[PRAAx] le (two*top k A R*unit t) (unit p)) →
      (Γ ⊢[PRAAx] distanceBounded (fullBeta p k A R K z B N) u (unit t+two*unit q) (unit t*unit q))) :
    Γ ⊢[PRAAx] distanceBounded u (improperPoint v z R B A)
      (numerator q v q0 R N*unit t+num 12*denominator q v q0 N) (denominator q v q0 N*unit t) := by
  let k := cutoff t A N
  let H := GaussianBetaSharpCofinalSchedule.minimumH t z R B A N
  let K := factor t H A R N
  let p := GaussianBetaSharpCofinalSchedule.minimumPrecision t H z R B A N
  have hCut := GaussianBetaSharpCofinalSchedule.cutoff_bounds (Γ := Γ) t A R N
  have hN := GaussianBetaSharpNaturalDegreeSchedule.degree_positive z R B A N h
  have hK := GaussianBetaSharpCofinalSchedule.factor_positive (Γ := Γ) t H z R B A N (le_refl H)
  have hm := GaussianBetaSharpCofinalSchedule.mesh_budgets (Γ := Γ) t H z R B A N (le_refl H)
  have hp := GaussianBetaSharpCofinalSchedule.precision_budgets (Γ := Γ) p t H z R B A N (le_refl p)
  have ht := GaussianBetaSharpCofinalSchedule.finite_binding_time_budget (Γ := Γ) p t H z R B A N (le_refl p)
  have finite := bind p k K hCut.andE₂.andE₂ hK hCut.andE₂.andE₁
    (GaussianBetaSharpNaturalDegreeSchedule.support_cells t H z R B A N h (le_refl H)) hp.andE₂.andE₁ ht
  have improper := GaussianBetaSharpFiniteBinding.original_improper_euler t p v k z R B A H
    (.andI h.andE₁.andE₂.andE₁ h.andE₁) hm.andE₁ hCut.andE₁ hp.andE₂.andE₂.andE₁
  exact GaussianEulerSharpResidualAssembly.sampler_distance
    u (fullBeta p k A R K z B N) (fullEuler p k A R K z B) (improperPoint v z R B A) _ _ _ _ _
    (positive_product _ _ hN (fixed_denominator_positive q0 N)) (unit_positive q) (unit_positive v) (unit_positive t)
    finite (GaussianEulerSharpGridRate.original_grids t q0 z R B A N h) improper

/-- Remove the auxiliary grid error using the same explicit finite precision for either sampler. -/
theorem sharp_bound_of_cofinal (q v q0 R N u w : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : ∀ t : PTm n, Γ ⊢[PRAAx] distanceBounded u w
      (numerator q v q0 R N*unit t+num 12*denominator q v q0 N) (denominator q v q0 N*unit t)) :
    Γ ⊢[PRAAx] distanceBounded u w (numerator q v q0 R N) (denominator q v q0 N) := by
  let diff := qsub u w
  let X := numerator q v q0 R N
  let Y := denominator q v q0 N
  have hY : Γ ⊢[PRAAx] le one Y :=
    positive_product _ _ (positive_product _ _ hN (fixed_denominator_positive q0 N))
      (positive_product _ _ (unit_positive q) (unit_positive v))
  exact GaussianRationalSlackRemoval.slack_removal_at diff X Y (num 12) hY
    (h (GaussianRationalSlackRemoval.precision diff X Y (num 12)))

/-- Every working precision has a concrete common mesh and sample clock
satisfying the original three panel estimates and both sampler bindings. -/
theorem cofinal_observations (t q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A N) (improperPoint v z R B A)
      (numerator q v q0 R N*unit t+num 12*denominator q v q0 N) (denominator q v q0 N*unit t) :=
  cofinal_observations_of_finite_binding t q v q0 z R B A N (finitePoint q z R B A N)
    (.andI h.andE₁ (GaussianBetaSharpCofinalSchedule.degree_two z R B A N h))
    (fun p k K => GaussianBetaSharpFiniteBinding.original_finite_euler t p q k z R B A N K h)

/-- The original finite Euler name and the original improper Euler name satisfy
the sharp two-term rate. The decay-name error is one D_R times its requested
observation tolerance, while the two output queries have their own tolerances. -/
theorem original_sharp_bound (q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A N) (improperPoint v z R B A)
      (numerator q v q0 R N) (denominator q v q0 N) :=
  sharp_bound_of_cofinal q v q0 R N (finitePoint q z R B A N) (improperPoint v z R B A)
    (GaussianBetaFiniteEulerComparison.degree_positive z R B A N h)
    (fun t => cofinal_observations t q v q0 z R B A N h)

theorem actual_finite_Euler_sharp_rate_to_original_improper_integral_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (finitePoint (var 0) (var 3) (var 4) (var 5) (var 6) (var 7))
          (improperPoint (var 1) (var 3) (var 4) (var 5) (var 6))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 7))
          (denominator (var 0) (var 1) (var 2) (var 7))) :=
  closeUniv 8 (.impI (original_sharp_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpFiniteRate
