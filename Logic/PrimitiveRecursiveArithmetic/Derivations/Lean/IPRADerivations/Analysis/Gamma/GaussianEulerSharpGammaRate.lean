import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpFiniteRate
import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification

/-!
# Transfer of the exact finite Euler rate to the original Gamma name

The exact sharp radius survives replacement of the original improper
Euler name by its independently chosen original Gamma observation.
The intermediate Euler clock is chosen by finite rational slack removal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpGammaRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerSharpFiniteRate (finitePoint improperPoint numerator denominator)
open GaussianBetaSharpCofinalSchedule (source)
open GaussianBetaContiguousUpperTailBudget (fixed_denominator_positive)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerSharpResidualAssembly (boundNumerator boundDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gammaPoint (v z R B A : PTm n) : PTm n := ap2 gammaF v (gammaData z R B A)

private theorem transfer_radius (a b c X Y P V U : PTm n)
    (hY : Γ ⊢[PRAAx] le one Y) (hP : Γ ⊢[PRAAx] le one P)
    (hV : Γ ⊢[PRAAx] le one V) (hU : Γ ⊢[PRAAx] le one U)
    (hab : Γ ⊢[PRAAx] distanceBounded a b
      (GaussianEulerSharpResidualAssembly.boundNumerator X Y P U)
      (GaussianEulerSharpResidualAssembly.boundDenominator Y P U))
    (hbc : Γ ⊢[PRAAx] distanceBounded b c (U+V) (U*V)) : Γ ⊢[PRAAx]
    distanceBounded a c (GaussianEulerSharpResidualAssembly.boundNumerator X Y P V*U+
      two*GaussianEulerSharpResidualAssembly.boundDenominator Y P V)
      (GaussianEulerSharpResidualAssembly.boundDenominator Y P V*U) := by
  have h₁ := positive_product Y (P*U) hY (positive_product _ _ hP hU)
  have h₂ := positive_product U V hU hV
  have h₃ := positive_product Y (P*V) hY (positive_product _ _ hP hV)
  have sum := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ h₁ h₂ hab hbc
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ h₁ h₂) (positive_product _ _ h₃ hU)
    (le_congr (by unfold boundNumerator boundDenominator; ipra_ring) (.eqRefl _) (le_refl _)) sum

theorem original_finite_euler_to_gamma (q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A N) (gammaPoint v z R B A)
      (numerator q v q0 R N) (denominator q v q0 N) := by
  let a := finitePoint q z R B A N
  let c := gammaPoint v z R B A
  let X := numerator q v q0 R N
  let Y := denominator q v q0 N
  let t := GaussianRationalSlackRemoval.precision (qsub a c) X Y two
  have hN := GaussianBetaFiniteEulerComparison.degree_positive z R B A N h
  have hD := positive_product N _ hN (fixed_denominator_positive q0 N)
  have hY : Γ ⊢[PRAAx] le one Y :=
    positive_product _ _ hD (positive_product _ _ (unit_positive q) (unit_positive v))
  have eqv := GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A
    (.andI h.andE₁ h.andE₂.andE₁)
  have hbc := GaussianNameEquivalence.cross_at _ _ _ _ t v eqv
  have hab := GaussianEulerSharpFiniteRate.original_sharp_bound q t q0 z R B A N h
  exact GaussianRationalSlackRemoval.slack_removal_at (qsub a c) X Y two hY
    (transfer_radius a (improperPoint t z R B A) c _ _ _ _ _ hD
      (unit_positive q) (unit_positive v) (unit_positive t) hab hbc)

theorem original_finite_Euler_sharp_rate_to_Gamma_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (finitePoint (var 0) (var 3) (var 4) (var 5) (var 6) (var 7))
          (gammaPoint (var 1) (var 3) (var 4) (var 5) (var 6))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 7))
          (denominator (var 0) (var 1) (var 2) (var 7))) :=
  closeUniv 8 (.impI (original_finite_euler_to_gamma _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpGammaRate
