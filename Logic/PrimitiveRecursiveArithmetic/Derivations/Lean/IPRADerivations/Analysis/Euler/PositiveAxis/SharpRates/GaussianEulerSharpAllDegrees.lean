import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaAllDegreeFiniteBinding
import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpGridRate
import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpFiniteRate

/-!
# The sharp Euler integral comparison at every degree at least two

The same finite reciprocal evaluator uses an inverse height certified
from its finite beta endpoint. This height works even below twice the
disk radius. The original and endpoint-certified heights give equivalent
names on the domain where the original height was certified.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpAllDegrees

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpNaturalDegreeSchedule (source)
open GaussianBetaSharpCofinalSchedule (cutoff factor)
open GaussianEulerSharpFiniteRate (improperPoint numerator denominator)
open GaussianBetaSharpFiniteBinding (fullBeta fullEuler)
open GaussianBetaContiguousUpperTailBudget (fixed_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finitePoint (q z B N : PTm n) : PTm n :=
  ap2 GaussianBetaAllDegreeEulerInverse.nameF q (GaussianBetaAllDegreeEulerInverse.data z B N)

theorem cofinal_observations (t q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z B N) (improperPoint v z R B A)
      (numerator q v q0 R N*unit t+num 12*denominator q v q0 N) (denominator q v q0 N*unit t) := by
  let k := cutoff t A N
  let H := GaussianBetaSharpCofinalSchedule.minimumH t z R B A N
  let K := factor t H A R N
  let p := GaussianBetaSharpCofinalSchedule.minimumPrecision t H z R B A N
  have hN := GaussianBetaSharpNaturalDegreeSchedule.degree_positive z R B A N h
  have hCut := GaussianBetaSharpCofinalSchedule.cutoff_bounds (Γ := Γ) t A R N
  have hK := GaussianBetaSharpCofinalSchedule.factor_positive (Γ := Γ) t H z R B A N (le_refl H)
  have hm := GaussianBetaSharpCofinalSchedule.mesh_budgets (Γ := Γ) t H z R B A N (le_refl H)
  have hp := GaussianBetaSharpCofinalSchedule.precision_budgets (Γ := Γ) p t H z R B A N (le_refl p)
  have ht := GaussianBetaSharpCofinalSchedule.finite_binding_time_budget (Γ := Γ) p t H z R B A N (le_refl p)
  have hU := unit_positive (Γ := Γ) t
  have bd := positive_product _ _ hN (fixed_denominator_positive q0 N)
  have grid := GaussianEulerSharpGridRate.original_grids t q0 z R B A N h
  have finite := GaussianBetaAllDegreeFiniteBinding.original_finite_euler t p q k z R B A N K
    (.andI h.andE₁ hN) hCut.andE₂.andE₂ hK hCut.andE₂.andE₁
    (GaussianBetaSharpNaturalDegreeSchedule.support_cells t H z R B A N h (le_refl H))
    hp.andE₂.andE₁ ht
  have improper := GaussianBetaSharpFiniteBinding.original_improper_euler t p v k z R B A H
    (.andI h.andE₁.andE₂.andE₁ h.andE₁) hm.andE₁ hCut.andE₁ hp.andE₂.andE₂.andE₁
  exact GaussianEulerSharpResidualAssembly.sampler_distance
    (finitePoint q z B N) (fullBeta p k A R K z B N) (fullEuler p k A R K z B) (improperPoint v z R B A)
    _ _ _ _ _ bd (unit_positive q) (unit_positive v) hU finite grid improper

theorem original_sharp_bound (q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z B N) (improperPoint v z R B A)
      (numerator q v q0 R N) (denominator q v q0 N) := by
  let diff := qsub (finitePoint q z B N) (improperPoint v z R B A)
  let X := numerator q v q0 R N
  let Y := denominator q v q0 N
  let t := GaussianRationalSlackRemoval.precision diff X Y (num 12)
  have hN := GaussianBetaSharpNaturalDegreeSchedule.degree_positive z R B A N h
  have hY : Γ ⊢[PRAAx] le one Y :=
    positive_product _ _ (positive_product _ _ hN (fixed_denominator_positive q0 N))
      (positive_product _ _ (unit_positive q) (unit_positive v))
  exact GaussianRationalSlackRemoval.slack_removal_at diff X Y (num 12) hY
    (cofinal_observations t q v q0 z R B A N h)

theorem original_sharp_Euler_integral_rate_every_degree_two_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (finitePoint (var 0) (var 3) (var 5) (var 7))
          (improperPoint (var 1) (var 3) (var 4) (var 5) (var 6))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 7))
          (denominator (var 0) (var 1) (var 2) (var 7))) :=
  closeUniv 8 (.impI (original_sharp_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpAllDegrees
