import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingNativeDuplication
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithmScale
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Normalization.GaussianGaussMultiplicationHalfPower
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames

/-!
# Logarithmic duplication on the original positive Gamma names

Recovering the three Gamma arguments and the half-argument factor by
exponentiating their actual logarithm programs turns the explicit
duplication identity into an equality of exponentials. Real injectivity
then gives the exact logarithmic duplication law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingLogDuplication

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedPositiveLogarithmScale (sum_axis)
open GaussianRealNameExponentialInjectivity (axisSamples independent_radii_injective)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_regular logGammaF logGammaData log_gamma_axis log_gamma_regular
  log_input gammaRetimedF gammaRetimedData gamma_retimed_cross)
open GaussianStirlingNativeDuplication (halfNumerator halfDenominator half_source double_source native_duplication)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def powerExponentF : PR 2 := GaussianGaussMultiplicationHalfPower.exponentF
def powerExponentData (a b : PTm n) : PTm n :=
  GaussianGaussMultiplicationHalfPower.exponentData (GaussianGaussMultiplicationPowerRate.multiplier (arg a) b two) two

abbrev leftF : PR 2 := addF logGammaF logGammaF
def leftData (a b : PTm n) : PTm n :=
  addData (logGammaData a b) (logGammaData (halfNumerator a b) (halfDenominator b))
abbrev rightInnerF : PR 2 := addF powerExponentF logGammaF
def rightInnerData (a b : PTm n) : PTm n := addData (powerExponentData a b) (logGammaData one two)
abbrev rightF : PR 2 := addF rightInnerF logGammaF
def rightData (a b : PTm n) : PTm n := addData (rightInnerData a b) (logGammaData (two*a) b)

theorem exponential_sum (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E f) (E g)) (E (addF f g))
      (multiplyData (E f) (E g) (ed f x) (ed g y)) (ed (addF f g) (addData x y)) := by
  have h := add_fast f g x y hf hg
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent f g (addF f g)
    (U f x) (U g y) (U (addF f g) (addData x y)) x y (addData x y)
    (exponential_input f x hf) (exponential_input g y hg) (exponential_input _ _ h) (cross_refl _ _ h)

theorem exponential_gamma (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (E logGammaF) gammaF (ed logGammaF (logGammaData a b)) (gammaData a b) := by
  have h := log_input a b hs
  have ex := GaussianNamedPositiveLogarithm.exponential_input _ _ _ _ h
  have out := GaussianNamedPositiveLogarithmExponential.original_recovery _ _ _ _ h
  have changeClock := GaussianExponentialRadiusIndependence.same_input_cross logGammaF
    (U logGammaF (logGammaData a b)) _ (logGammaData a b)
    (exponential_input _ _ (log_gamma_regular a b hs)) ex
  exact cross_trans _ _ _ _ _ _ changeClock (cross_trans _ _ _ _ _ _ out
    (cross_symm _ _ _ _ (gamma_retimed_cross a b hs)))

theorem exponential_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (E f) (ed f x) :=
  GaussianRadiusExponentialName.name_regular f (U f x) x (exponential_input _ _ h)

theorem power_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN powerExponentF (powerExponentData a b) :=
  GaussianGaussMultiplicationHalfPower.exponent_regular _ _ (le_succ_self one)

theorem power_axis (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] axisSamples powerExponentF (powerExponentData a b) := by
  let c := GaussianGaussMultiplicationPowerRate.multiplier (arg a) b two
  have e : Γ ⊢[PRAAx] GaussianRationalHorner.ofGaussian (ComplexLogarithmRemainder.scale two (arg a)) b ≐
      GaussianPositiveRationalLogarithm.fraction (two*a) b :=
    GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hs.andE₂ (GaussianStirlingNativeDuplication.scale_argument _ _)
  have axis := RationalGaussianEmbedding.axis_congr e.eqSymm (GaussianStirlingNames.fraction_axis (two*a) b hs.andE₂)
  have hc : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis c := RationalGaussianEmbedding.axis_add _ _ axis
    (RationalGaussianEmbedding.axis_negative _ RationalGaussianEmbedding.axis_one)
  have all := GaussianGaussMultiplicationHalfPower.exponent_real c two hc
  refine .allI ?_
  have shifted : Γ.map Fm.shift ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples powerExponentF
      (Syn.shift (powerExponentData a b)) := by
    simpa only [Fm.shift,Syn.shift,GaussianSignedNameExponentialOrder.subst_realSamples,c,powerExponentF,powerExponentData] using all.shift
  exact (GaussianSignedNameExponentialOrder.real_sample_at powerExponentF _ (var 0) shifted).andE₂

set_option maxHeartbeats 1800000 in
theorem logarithmic_duplication (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData a b) (rightData a b) := by
  let c := halfNumerator a b
  let d := halfDenominator b
  let x := logGammaData a b
  let y := logGammaData c d
  let z := logGammaData (two*a) b
  let v : PTm n := logGammaData one two
  let w := powerExponentData a b
  let l := leftData a b
  let r := rightData a b
  let q := rightInnerData a b
  let G := logGammaF
  let P := powerExponentF
  let F := GaussianGaussMultiplicationPowerRate.powerF
  let t := GaussianGaussMultiplicationPowerPerturbation.limitData (arg a) a b two
  have sh := half_source a b hs
  have sd := double_source a b hs
  have so : Γ ⊢[PRAAx] source one two := .andI (le_refl one) (le_succ_self one)
  have hx := log_gamma_regular a b hs
  have hy := log_gamma_regular c d sh
  have hz := log_gamma_regular _ _ sd
  have hv := log_gamma_regular _ _ so
  have hw := power_regular (Γ := Γ) a b
  have hq : Γ ⊢[PRAAx] pointCN rightInnerF q := add_fast P G w v hw hv
  have hL : Γ ⊢[PRAAx] pointCN leftF l := add_fast G G x y hx hy
  have hR : Γ ⊢[PRAAx] pointCN rightF r := add_fast rightInnerF G q z hq hz
  have left := multiply_cross (E G) gammaF (E G) gammaF (ed G x) (gammaData a b) (ed G y) (gammaData c d)
    (exponential_regular G x hx) (gamma_regular a b hs) (exponential_regular G y hy) (gamma_regular c d sh)
    (exponential_gamma a b hs) (exponential_gamma c d sh)
  have power := GaussianGaussMultiplicationHalfPower.original_limit_power (arg a) a b two (le_succ_self one)
    hs.andE₂ (GaussianStirlingGammaLogarithm.native_disk a b hs)
  have powerReg : Γ ⊢[PRAAx] pointCN F t := cross_trans _ _ _ _ _ _ power (cross_symm _ _ _ _ power)
  have half := gamma_regular one two so
  have qExp := exponential_sum P G w v hw hv
  have pair := multiply_cross F (E P) gammaF (E G) t (ed P w) (gammaData one two) (ed G v)
    powerReg (exponential_regular P w hw) half (exponential_regular G v hv) power
    (cross_symm _ _ _ _ (exponential_gamma one two so))
  have qIdentity := cross_trans _ _ _ _ _ _ pair qExp
  have right := multiply_cross (multiplyF F gammaF) (E rightInnerF) gammaF (E G)
    (multiplyData F gammaF t (gammaData one two)) (ed rightInnerF q) (gammaData (two*a) b) (ed G z)
    (multiply_fast _ _ _ _ powerReg half) (exponential_regular _ _ hq) (gamma_regular _ _ sd)
    (exponential_regular _ _ hz) qIdentity (cross_symm _ _ _ _ (exponential_gamma _ _ sd))
  have e := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_sum G G x y hx hy))
    (cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ (native_duplication a b hs)
      (cross_trans _ _ _ _ _ _ right (exponential_sum rightInnerF G q z hq hz))))
  exact independent_radii_injective leftF rightF (U leftF l) (U rightF r) l r
    (exponential_input _ _ hL) (exponential_input _ _ hR)
    (sum_axis G G x y (log_gamma_axis a b) (log_gamma_axis c d))
    (sum_axis rightInnerF G q z (sum_axis P G w v (power_axis a b hs) (log_gamma_axis one two))
      (log_gamma_axis (two*a) b)) e

set_option maxHeartbeats 1800000 in
theorem actual_positive_rational_log_Gamma_duplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent leftF rightF (leftData (var 0) (var 1)) (rightData (var 0) (var 1))) :=
  closeUniv 2 (.impI (logarithmic_duplication _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingLogDuplication
