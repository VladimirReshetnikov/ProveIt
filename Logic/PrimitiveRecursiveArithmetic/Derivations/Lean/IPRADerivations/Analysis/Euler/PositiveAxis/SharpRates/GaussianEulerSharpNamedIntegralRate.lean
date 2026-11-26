import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpNamedSchedule
import IPRADerivations.Analysis.Euler.GaussianNamedEulerQuadrature

/-!
# The exact sharp rate to the original named improper Euler integral

Replace named Gamma by the proved original named Euler integral without
changing either leading term or either independently requested error.
The actual quadrature is exposed at its unchanged name clock v+3.
The literal degree also yields the evaluated 2^-p approximation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpNamedIntegralRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (radius)
open GaussianEulerSharpNamedRate (source finitePoint baseNumerator baseDenominator)
open GaussianEulerSharpFiniteRate (numerator denominator)
open GaussianEulerSharpResidualAssembly (boundNumerator boundDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def improperPoint (f : PR 2) (v x A : PTm n) : PTm n :=
  ap2 (GaussianNamedEulerQuadrature.nameF f) v (GaussianNamedGamma.data x A)

theorem transfer_radius (a b c X Y P V U : PTm n)
    (hY : Γ ⊢[PRAAx] le one Y) (hP : Γ ⊢[PRAAx] le one P)
    (hV : Γ ⊢[PRAAx] le one V) (hU : Γ ⊢[PRAAx] le one U)
    (hab : Γ ⊢[PRAAx] distanceBounded a b (boundNumerator X Y P U) (boundDenominator Y P U))
    (hbc : Γ ⊢[PRAAx] distanceBounded b c (U+V) (U*V)) : Γ ⊢[PRAAx]
    distanceBounded a c (boundNumerator X Y P V*U+two*boundDenominator Y P V)
      (boundDenominator Y P V*U) := by
  have h₁ := positive_product Y (P*U) hY (positive_product _ _ hP hU)
  have h₂ := positive_product U V hU hV
  have h₃ := positive_product Y (P*V) hY (positive_product _ _ hP hV)
  have sum := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ h₁ h₂ hab hbc
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ h₁ h₂) (positive_product _ _ h₃ hU)
    (le_congr (by dsimp only [boundNumerator,boundDenominator]; ipra_ring) (.eqRefl _) (le_refl _)) sum

theorem original_sharp_bound (f : PR 2) (p v q0 x A N : PTm n) (h : Γ ⊢[PRAAx] source f x A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f p x A N) (improperPoint f v x A)
      (numerator p v q0 (radius f x) N) (denominator p v q0 N) := by
  let a := finitePoint f p x A N
  let c := improperPoint f v x A
  let X := numerator p v q0 (radius f x) N
  let Y := denominator p v q0 N
  let t := GaussianRationalSlackRemoval.precision (qsub a c) X Y two
  have hN : Γ ⊢[PRAAx] le one N := le_trans (le_succ_self one) h.andE₂
  have hD : Γ ⊢[PRAAx] le one (baseDenominator q0 N) :=
    positive_product _ _ hN (GaussianBetaContiguousUpperTailBudget.fixed_denominator_positive q0 N)
  have hY : Γ ⊢[PRAAx] le one Y := positive_product _ _ hD (positive_product _ _ (unit_positive p) (unit_positive v))
  have equivalence := GaussianNameEquivalence.cross_symm _ _ _ _
    (GaussianNamedEulerQuadrature.original_named_Euler_integral_is_Gamma f x A h.andE₁)
  have middle := GaussianNameEquivalence.cross_at _ _ _ _ t v equivalence
  have finite := GaussianEulerSharpNamedRate.original_sharp_bound f p t q0 x A N h
  exact GaussianRationalSlackRemoval.slack_removal_at (qsub a c) X Y two hY
    (transfer_radius a (GaussianEulerSharpNamedRate.gammaPoint f t x A) c
      (baseNumerator q0 (radius f x) N) (baseDenominator q0 N) (unit p) (unit v) (unit t)
      hD (unit_positive p) (unit_positive v) (unit_positive t) finite middle)

theorem original_grid_observations (f : PR 2) (p v q0 x A N : PTm n) (h : Γ ⊢[PRAAx] source f x A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f p x A N) (GaussianNamedEulerQuadrature.original f (GaussianNamedEulerQuadrature.retimed v) x A)
      (numerator p v q0 (radius f x) N) (denominator p v q0 N) :=
  distance_congr (.eqRefl _) (GaussianNamedEulerQuadrature.name_at f v x A) (.eqRefl _) (.eqRefl _)
    (original_sharp_bound f p v q0 x A N h)

theorem original_scheduled_observations (f : PR 2) (p q v x A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f q x A (GaussianEulerSharpDegreeSchedule.degree p (radius f x))) (improperPoint f v x A)
      (GaussianEulerSharpScheduledApproximation.numerator p q v) (GaussianEulerSharpScheduledApproximation.denominator p q v) :=
  GaussianEulerSharpScheduledApproximation.numerical_rate p q v
    (GaussianEulerSharpScheduleBudget.mainNumerator p (radius f x)) (GaussianEulerSharpScheduleBudget.mainDenominator p (radius f x)) _ _
    (positive_product _ _ (GaussianEulerSharpDegreeSchedule.degree_positive _ _)
      (GaussianBetaContiguousUpperTailBudget.fixed_denominator_positive _ _))
    (GaussianEulerSharpScheduleBudget.main_budget p (radius f x))
    (original_sharp_bound f q v (GaussianEulerSharpScheduleBudget.decayClock p (radius f x)) x A
      (GaussianEulerSharpDegreeSchedule.degree p (radius f x)) (.andI h (GaussianEulerSharpNamedSchedule.degree_guard f p x)))

theorem original_scheduled_evaluated (f : PR 2) (p x A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f (p+num 2) x A (GaussianEulerSharpDegreeSchedule.degree p (radius f x)))
      (improperPoint f (p+num 2) x A) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (GaussianEulerSharpScheduledApproximation.denominator_positive p (p+num 2) (p+num 2))
    (unit_positive p) (GaussianEulerSharpScheduledApproximation.evaluated_precision_budget p)
    (original_scheduled_observations f p (p+num 2) (p+num 2) x A h)

theorem original_scheduled_grid_evaluated (f : PR 2) (p x A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f (p+num 2) x A (GaussianEulerSharpDegreeSchedule.degree p (radius f x)))
      (GaussianNamedEulerQuadrature.original f (GaussianNamedEulerQuadrature.retimed (p+num 2)) x A) one (unit p) :=
  distance_congr (.eqRefl _) (GaussianNamedEulerQuadrature.name_at f (p+num 2) x A) (.eqRefl _) (.eqRefl _)
    (original_scheduled_evaluated f p x A h)

theorem original_named_improper_Euler_exact_sharp_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source f (var 3) (var 4) (var 5) ⟶
      distanceBounded (finitePoint f (var 0) (var 3) (var 4) (var 5)) (improperPoint f (var 1) (var 3) (var 4))
        (numerator (var 0) (var 1) (var 2) (radius f (var 3)) (var 5)) (denominator (var 0) (var 1) (var 2) (var 5))) :=
  closeUniv 6 (.impI (original_sharp_bound f _ _ _ _ _ _ Prf.hyp0))
theorem original_named_Euler_literal_sharp_degree_grid_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianNamedRightHalfPlane.source f (var 1) (var 2) ⟶
      distanceBounded (finitePoint f ((var 0)+num 2) (var 1) (var 2) (GaussianEulerSharpDegreeSchedule.degree (var 0) (radius f (var 1))))
        (GaussianNamedEulerQuadrature.original f (GaussianNamedEulerQuadrature.retimed ((var 0)+num 2)) (var 1) (var 2)) one (unit (var 0))) :=
  closeUniv 3 (.impI (original_scheduled_grid_evaluated f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpNamedIntegralRate
