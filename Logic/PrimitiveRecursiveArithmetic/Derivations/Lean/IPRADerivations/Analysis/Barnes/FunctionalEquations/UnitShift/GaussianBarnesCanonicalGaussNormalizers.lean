import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalAdjacentLog
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntegerExponential
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingGammaLogarithm

/-!
# Exact factorial and power normalizers in the Barnes recurrence

The exponentiated original Stirling log-Gamma observation at `N+1`
equals the actual factorial constant. The original Euler logarithm
at `K`, multiplied by `K` and exponentiated, is the exact power `K^K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalGaussNormalizers

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (logF log_regular exponentialInputData exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (power)
open GaussianRootAlgebra (equal equal_of_values equal_trans re_add im_add re_scale im_scale re_one im_one)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "C" => constantF

private theorem factorial_argument (N : PTm n) : Γ ⊢[PRAAx]
    equal (GaussianGammaFactorialValues.argument N) (GaussianStirlingGammaLogarithm.arg (succ N)) := by
  apply equal_trans (GaussianGammaShiftTrajectory.point_native oneCode one N)
  apply equal_of_values <;> simp only [translated,GaussianStirlingGammaLogarithm.arg,re_add,im_add,re_scale,im_scale,
    re_one,im_one] <;> ipra_simps <;> ring

theorem factorial_log_exponential (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (E GaussianStirlingGammaLogarithm.logGammaF) C
      (ed GaussianStirlingGammaLogarithm.logGammaF (GaussianStirlingGammaLogarithm.logGammaData (succ N) one)) (naturalPoint (fact N)) := by
  let K := succ N
  let F := GaussianStirlingGammaLogarithm.logGammaF
  let X := GaussianStirlingGammaLogarithm.logGammaData K one
  let U' := GaussianStirlingGammaLogarithm.gammaRetimedF
  let Y := GaussianStirlingGammaLogarithm.gammaRetimedData K one
  let M : PTm n := GaussianStirlingGammaLogarithm.gammaLogMargin
  let T := U GaussianStirlingGammaLogarithm.gammaRealF (GaussianStirlingGammaLogarithm.gammaData K one)
  let R := GaussianCompactLogarithmBounds.radius M T
  let z := GaussianGammaFactorialValues.argument N
  let w := GaussianStirlingGammaLogarithm.arg K
  have src : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source K one := .andI (zero_lt_succ N) (le_refl one)
  have a := GaussianStirlingGammaLogarithm.log_input K one src
  have hR := GaussianNamedPositiveLogarithm.exponential_input U' Y M T a
  have hU := exponential_input F X (GaussianStirlingGammaLogarithm.log_gamma_regular K one src)
  have e := GaussianExponentialRadiusIndependence.same_input_cross F (U F X) R X hU hR
  have logEq := GaussianNamedPositiveLogarithmExponential.original_recovery U' Y M T a
  have back := cross_symm _ _ _ _ (GaussianStirlingGammaLogarithm.gamma_retimed_cross K one src)
  have chart := GaussianGammaInputProperness.original_Gamma_proper w z K one one one
    (GaussianStirlingGammaLogarithm.gamma_source K one src) (GaussianRootAlgebra.equal_symm (factorial_argument N))
  have order : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.gammaData z K one one ≐ GaussianGammaFactorialValues.data N := by
    ipra_congr (GaussianGammaReciprocalInverse.gammaData (var 0) (var 1) one one : PTm 2) with
      [.eqRefl z, (by dsimp only [K,GaussianGammaFactorialValues.radius]; ipra_ring : Γ ⊢[PRAAx] K ≐ GaussianGammaFactorialValues.radius N)]
      using [GaussianGammaFactorialValues.data,GaussianGammaFactorialValues.argument,z,one]
  have adjusted := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ order.eqSymm (.eqRefl _)
    (GaussianGammaFactorialValues.original_C21_factorial N)
  exact cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _ logEq
    (cross_trans _ _ _ _ _ _ back (cross_trans _ _ _ _ _ _ chart adjusted)))

abbrev integerLogF : PR 2 := multiplyF C logF
def integerLogData (K : PTm n) : PTm n := multiplyData C logF (naturalPoint K) K
def integerExpData (K : PTm n) : PTm n := ed integerLogF (integerLogData K)

theorem integer_log_exponential (K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    crossEquivalent (E integerLogF) C (integerExpData K) (power (naturalPoint K) K) := by
  let L := GaussianPositiveRationalLogarithm.logF
  let A := GaussianPositiveRationalLogarithm.data K one
  let x := integerLogData K
  let F := GaussianHarmonicIntegerExponential.originalExponentF
  let y := GaussianHarmonicIntegerExponential.originalExponentData K K one
  have src : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source K one := .andI hK (le_refl _)
  have bounds : Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source K one one K :=
    .andI (le_refl _) (.andI src (.andI (le_congr (.eqRefl _) (by ipra_ring) hK)
      (le_congr (.eqRefl _) (by ipra_ring) (le_refl K))))
  have hx := log_regular K hK
  have hy := GaussianPositiveRationalLogarithm.name_regular K one src
  have c := constant_regular (Γ := Γ) (naturalPoint K)
  have e : Γ ⊢[PRAAx] crossEquivalent integerLogF F x y :=
    GaussianGammaAdjacentCutoff.multiply_cross C C logF L (naturalPoint K) (naturalPoint K) K A c c hx hy
      (cross_refl _ _ c) (cross_symm _ _ _ _ (GaussianBetaUpperPowerCancellation.rational_log_integer K hK))
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper integerLogF F (U integerLogF x) (U F y) x y
    (exponential_input _ _ (multiply_fast _ _ _ _ c hx)) (exponential_input _ _ (multiply_fast _ _ _ _ c hy)) e
  have result := GaussianHarmonicIntegerExponential.original_integer_exponential K K one one K bounds
  exact cross_trans _ _ _ _ _ _ exp (cross_trans _ _ _ _ _ _ result
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianHarmonicIntegerExponential.actual_rational_power K one K (le_refl one)).eqSymm))

theorem actual_Barnes_factorial_logarithm_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let N := var 0
     crossEquivalent (E GaussianStirlingGammaLogarithm.logGammaF) C
       (ed GaussianStirlingGammaLogarithm.logGammaF (GaussianStirlingGammaLogarithm.logGammaData (succ N) one)) (naturalPoint (fact N))) :=
  closeUniv 1 (factorial_log_exponential _)

theorem actual_Barnes_integer_logarithm_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let K := var 0
     le one K ⟶ crossEquivalent (E integerLogF) C (integerExpData K) (power (naturalPoint K) K)) :=
  closeUniv 1 (.impI (integer_log_exponential _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalGaussNormalizers
