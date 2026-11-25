import IPRADerivations.Analysis.GaussianStirlingWallisLogRate
import IPRADerivations.Analysis.GaussianNamedProductSquare

/-!
# Exact Gamma logarithm identity for the Stirling Wallis half-step

Both sides are original real logarithm names. Exponentiating gives
the actual squared half-integer Gamma. The positivity certificate
permits recovery of the Wallis ratio from its named logarithm.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingWallisLogIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingWallisGammaRatio (halfNumerator halfData integerData halfSquareF halfSquareData half_source
  half_regular ratioF ratioData wallisF wallisData wallis_cross integerScaledF integerScaledData integer_divisor_cross)
open GaussianStirlingWallisFactor (integerDivisor inverseIntegerDivisor integer_divisor_positive)
open GaussianStirlingWallisLogRate (exponential_wall wallis_regular)
open GaussianStirlingLogDuplication (exponential_sum exponential_gamma exponential_regular)
open GaussianStirlingNames (logGammaF logGammaData log_gamma_regular logXF logXData log_x_regular log_x_real)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast addF addData add_fast)
open GaussianNameRingLaws (multiply_associative)
open GaussianNamedProductSquare (right_unit)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNameBounds (U)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedPositiveLogarithmScale (sum_axis)
open GaussianRealNameExponentialInjectivity (axisSamples independent_radii_injective)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "H" => GaussianStirlingWallisLogRate.nameF
local notation "L" => logGammaF
local notation "X" => logXF
local notation "C" => constantF
local notation "G" => gammaF

def doubleLogF : PR 2 := addF L L
def leftData (r : PTm n) : PTm n := addData (logGammaData (halfNumerator r) two) (logGammaData (halfNumerator r) two)
def doubleIntegerLogData (r : PTm n) : PTm n := addData (logGammaData (succ r) one) (logGammaData (succ r) one)
def denominatorLogF : PR 2 := addF X doubleLogF
def denominatorLogData (r : PTm n) : PTm n := addData (logXData (succ r) one) (doubleIntegerLogData r)
def rightF : PR 2 := addF H denominatorLogF
def rightData (r x : PTm n) : PTm n := addData (GaussianStirlingWallisLogRate.data r x) (denominatorLogData r)

@[simp] theorem subst_leftData {l : ℕ} (σ : Fin n → PTm l) (r : PTm n) :
    Syn.subst σ (leftData r) = leftData (Syn.subst σ r) := by simp [leftData,two,one]
@[simp] theorem subst_rightData {l : ℕ} (σ : Fin n → PTm l) (r x : PTm n) :
    Syn.subst σ (rightData r x) = rightData (Syn.subst σ r) (Syn.subst σ x) :=
  by simp [rightData,denominatorLogData,doubleIntegerLogData,one]

private theorem reciprocal_code (r : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (inverseIntegerDivisor r) (naturalPoint (integerDivisor r)) ≐ qone := by
  let D := integerDivisor r
  have hD := integer_divisor_positive (Γ := Γ) r
  have product := GaussianEulerDampedTimeRate.fraction_product one D D one hD (le_refl one)
  have same := GaussianStirlingRationalTelescopers.fraction_same (one*D) (D*one) one one
    (GaussianRationalHorner.positive_product D one hD (le_refl one)) (le_refl one) (by ipra_ring)
  exact product.eqTrans (same.eqTrans GaussianGammaFactorialValues.natural_one)

theorem multiply_denominator (r x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF wallisF integerScaledF) halfSquareF
      (multiplyData wallisF integerScaledF (wallisData r x) (integerScaledData r)) (halfSquareData r) := by
  let S := halfSquareF
  let u := halfSquareData r
  let v := inverseIntegerDivisor r
  let z := naturalPoint (integerDivisor r)
  let a := halfData r
  let b := integerData r
  have ha := half_regular (Γ := Γ) r
  have hb : Γ ⊢[PRAAx] pointCN G b := GaussianStirlingGammaLogarithm.gamma_regular _ _ (.andI (zero_lt_succ r) (le_refl one))
  have hs : Γ ⊢[PRAAx] pointCN S u := multiply_fast _ _ _ _ ha ha
  have hv := constant_regular (Γ := Γ) v
  have hz := constant_regular (Γ := Γ) z
  have he : Γ ⊢[PRAAx] pointCN integerScaledF (integerScaledData r) :=
    multiply_fast _ _ _ _ (constant_regular _) (multiply_fast _ _ _ _ hb hb)
  have hR : Γ ⊢[PRAAx] pointCN ratioF (ratioData r) := multiply_fast S C u v hs hv
  have step := multiply_cross wallisF ratioF integerScaledF C (wallisData r x) (ratioData r) (integerScaledData r) z
    (wallis_regular r x) hR he hz (cross_symm _ _ _ _ (wallis_cross r x)) (integer_divisor_cross r)
  have assoc := multiply_associative S C C u v z hs hv hz
  have const : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C (multiplyData C C v z) qone :=
    cross_trans _ _ _ _ _ _ (constant_product_cross v z) (constant_data_cross _ _ (reciprocal_code r))
  have replace := multiply_cross S S (multiplyF C C) C u u (multiplyData C C v z) qone hs hs
    (multiply_fast _ _ _ _ hv hz) (constant_regular _) (cross_refl _ _ hs) const
  exact cross_trans _ _ _ _ _ _ step
    (cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ replace (right_unit S u hs)))

private theorem log_x_exp (r : PTm n) : Γ ⊢[PRAAx] crossEquivalent (E X) C
    (ed X (logXData (succ r) one)) (naturalPoint (succ r)) := by
  let N := succ r
  let d := logXData N one
  have hs : Γ ⊢[PRAAx] GaussianStirlingNames.source N one := .andI (zero_lt_succ r) (le_refl one)
  have dom : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain N one one N :=
    .andI hs (.andI (le_congr (.eqRefl _) (one_mul N).eqSymm hs.andE₁)
      (le_congr (.eqRefl _) (by ipra_ring) (le_refl N)))
  have same := GaussianExponentialRadiusIndependence.same_input_cross X (U X d) (GaussianHarmonicLogarithmName.radius one N) d
    (exponential_input _ _ (log_x_regular N one hs)) (GaussianHarmonicLogarithmName.common_input N one one N (le_refl one) dom)
  exact cross_trans _ _ _ _ _ _ same (GaussianHarmonicLogarithmName.original_exponential_fraction N one one N (le_refl one) dom)

private theorem exponential_double_gamma (a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingNames.source a b) :
    Γ ⊢[PRAAx] crossEquivalent (E doubleLogF) (multiplyF G G)
      (ed doubleLogF (addData (logGammaData a b) (logGammaData a b)))
      (multiplyData G G (GaussianStirlingGammaLogarithm.gammaData a b) (GaussianStirlingGammaLogarithm.gammaData a b)) := by
  let x := logGammaData a b
  let y := GaussianStirlingGammaLogarithm.gammaData a b
  have h := log_gamma_regular a b hs
  have hg := GaussianStirlingGammaLogarithm.gamma_regular a b hs
  have hx := exponential_regular L x h
  have e := exponential_gamma a b hs
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_sum L L x x h h))
    (multiply_cross _ _ _ _ (ed L x) y (ed L x) y hx hg hx hg e e)

private theorem denominator_exp (r : PTm n) : Γ ⊢[PRAAx] crossEquivalent (E denominatorLogF) integerScaledF
    (ed denominatorLogF (denominatorLogData r)) (integerScaledData r) := by
  let N := succ r
  let a := logXData N one
  let b := doubleIntegerLogData r
  let c := naturalPoint N
  let d := integerData r
  have h : Γ ⊢[PRAAx] GaussianStirlingNames.source N one := .andI (zero_lt_succ r) (le_refl one)
  have ha := log_x_regular N one h
  have hi := log_gamma_regular N one h
  have hb : Γ ⊢[PRAAx] pointCN doubleLogF b := add_fast L L _ _ hi hi
  have hg := GaussianStirlingGammaLogarithm.gamma_regular N one h
  have e := exponential_sum X doubleLogF a b ha hb
  have conv := multiply_cross (E X) C (E doubleLogF) (multiplyF G G) (ed X a) c (ed doubleLogF b) (multiplyData G G d d)
    (exponential_regular X a ha) (constant_regular _) (exponential_regular doubleLogF b hb)
    (multiply_fast _ _ _ _ hg hg) (log_x_exp r) (exponential_double_gamma N one h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e) conv

private theorem axis_of_real (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx] axisSamples f x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  exact (real_sample_at f _ (var 0) hs).andE₂

theorem logarithmic_identity (r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] crossEquivalent doubleLogF rightF (leftData r) (rightData r x) := by
  let N := succ r
  let a := halfNumerator r
  let y := logGammaData a two
  let i := logGammaData N one
  let t := logXData N one
  let z := GaussianStirlingWallisLogRate.data r x
  let d := denominatorLogData r
  let u := leftData r
  let v := rightData r x
  have hs : Γ ⊢[PRAAx] GaussianStirlingNames.source N one := .andI (zero_lt_succ r) (le_refl one)
  have hh := half_source (Γ := Γ) r
  have hi := log_gamma_regular N one hs
  have ht := log_x_regular N one hs
  have hy := log_gamma_regular a two hh
  have hz := GaussianStirlingWallisLogRate.name_regular r x hn
  have hd : Γ ⊢[PRAAx] pointCN denominatorLogF d := add_fast X doubleLogF t _ ht (add_fast L L i i hi hi)
  have hu : Γ ⊢[PRAAx] pointCN doubleLogF u := add_fast L L y y hy hy
  have hv : Γ ⊢[PRAAx] pointCN rightF v := add_fast H denominatorLogF z d hz hd
  have denEx := denominator_exp (Γ := Γ) r
  have denReg : Γ ⊢[PRAAx] pointCN integerScaledF (integerScaledData r) :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ denEx) denEx
  have swap := multiply_cross (E H) wallisF (E denominatorLogF) integerScaledF (ed H z) (wallisData r x)
    (ed denominatorLogF d) (integerScaledData r) (exponential_regular H z hz) (wallis_regular r x)
    (exponential_regular denominatorLogF d hd) denReg (exponential_wall r x hn) denEx
  have right := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_sum H denominatorLogF z d hz hd))
    (cross_trans _ _ _ _ _ _ swap (multiply_denominator r x))
  have left := exponential_double_gamma a two hh
  have hL := GaussianStirlingGammaLogarithm.log_gamma_axis (Γ := Γ) a two
  have hI := GaussianStirlingGammaLogarithm.log_gamma_axis (Γ := Γ) N one
  have hT := axis_of_real (Γ := Γ) X t (log_x_real N one)
  have hZ := axis_of_real (Γ := Γ) H z (GaussianStirlingWallisLogRate.name_real r x)
  exact independent_radii_injective doubleLogF rightF (U doubleLogF u) (U rightF v) u v
    (exponential_input _ _ hu) (exponential_input _ _ hv) (sum_axis L L y y hL hL)
    (sum_axis H denominatorLogF z d hZ (sum_axis X doubleLogF t _ hT (sum_axis L L i i hI hI)))
    (cross_trans _ _ _ _ _ _ left (cross_symm _ _ _ _ right))

theorem actual_Stirling_Wallis_log_ratio_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (num 6) (succ (var 1)) ⟶ crossEquivalent doubleLogF rightF (leftData (var 1)) (rightData (var 1) (var 0))) :=
  closeUniv 2 (.impI (logarithmic_identity _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingWallisLogIdentity
