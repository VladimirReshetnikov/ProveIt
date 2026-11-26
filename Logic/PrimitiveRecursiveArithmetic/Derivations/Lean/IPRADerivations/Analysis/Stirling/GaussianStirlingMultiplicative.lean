import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeAlgebra
import IPRADerivations.Analysis.Stirling.GaussianStirlingDuplicationConstant
import IPRADerivations.Analysis.Exponential.GaussianRealExponentialCompactLower
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalRealSamples

/-!
# Exact normalized Stirling ratio for positive rational arguments

Exponentiating the logarithmic remainder gives the original Gamma
value divided by the positive Stirling normalization. The reciprocal
name is certified by multiplication with the literal factors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGaussTriplicationPi (doubledPiF doubledPiData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (distributive multiply_associative multiply_one negativeF negativeData negative_fast oneF one_fast)
open GaussianStirlingNames (logGammaF logGammaData log_gamma_regular source point productF productData product_regular gammaData gamma_regular)
open GaussianStirlingLogDuplication (exponential_sum exponential_gamma exponential_regular)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData remainder_regular normalizationSumF normalizationSumData
  normalization_sum_regular normalizationF normalizationData normalization_regular logarithmic_cancellation)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "CF" => GaussianStirlingConstant.nameF
local notation "CD" => GaussianStirlingConstant.nameData

abbrev expRemainderF : PR 2 := E remainderF
def expRemainderData (a b x : PTm n) : PTm n := ed remainderF (remainderData a b x)
abbrev sqrtF : PR 2 := E CF
def sqrtData (x : PTm n) : PTm n := ed CF (CD x)
abbrev powerF : PR 2 := E productF
def powerData (a b : PTm n) : PTm n := ed productF (productData a b)
abbrev decayF : PR 2 := E (negativeF constantF)
def decayData (a b : PTm n) : PTm n := ed (negativeF constantF) (negativeData (point a b))
abbrev firstFactorsF : PR 2 := multiplyF sqrtF powerF
def firstFactorsData (a b x : PTm n) : PTm n := multiplyData sqrtF powerF (sqrtData x) (powerData a b)
abbrev denominatorF : PR 2 := multiplyF firstFactorsF decayF
def denominatorData (a b x : PTm n) : PTm n := multiplyData firstFactorsF decayF (firstFactorsData a b x) (decayData a b)
abbrev normalizationExpF : PR 2 := E normalizationF
def normalizationExpData (a b x : PTm n) : PTm n := ed normalizationF (normalizationData a b x)
abbrev reciprocalF : PR 2 := E (negativeF normalizationF)
def reciprocalData (a b x : PTm n) : PTm n := ed (negativeF normalizationF) (negativeData (normalizationData a b x))
abbrev quotientF : PR 2 := multiplyF gammaF reciprocalF
def quotientData (a b x : PTm n) : PTm n := multiplyData gammaF reciprocalF (gammaData a b) (reciprocalData a b x)

theorem sqrt_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN sqrtF (sqrtData x) :=
  exponential_regular _ _ (GaussianStirlingConstant.name_regular x)

theorem sqrt_real (x : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples sqrtF (sqrtData x) :=
  GaussianEulerVerticalRealSamples.original_exponential_real_samples CF (U CF (CD x)) (CD x)
    (GaussianStirlingConstant.name_real x)

theorem sqrt_positive (p x : PTm n) : Γ ⊢[PRAAx] RationalValueBounds.upper
    (GaussianEuclideanDistanceName.fraction one (pw (num 3) (U CF (CD x))))
    (fstT (ap2 sqrtF p (sqrtData x))) one (unit p) :=
  GaussianRealExponentialCompactLower.original_observation_lower CF p _ _
    (exponential_input _ _ (GaussianStirlingConstant.name_regular x)) (GaussianStirlingConstant.name_real x)

set_option maxHeartbeats 700000 in
theorem sqrt_square (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF sqrtF sqrtF) doubledPiF
    (multiplyData sqrtF sqrtF (sqrtData x) (sqrtData x)) (doubledPiData x) := by
  let L := GaussianStirlingConstant.logDoubledPiF
  let W := GaussianStirlingConstant.logDoubledPiData x
  let B := addF CF CF
  let Y := addData (CD x) (CD x)
  let c : PTm n := GaussianPositiveRationalLogarithm.fraction one two
  let P := multiplyF constantF (addF L L)
  let Z := multiplyData constantF (addF L L) c (addData W W)
  have hc := GaussianStirlingConstant.name_regular (Γ := Γ) x
  have hl := GaussianStirlingConstant.log_doubled_regular (Γ := Γ) x
  have hB : Γ ⊢[PRAAx] pointCN B Y := add_fast _ _ _ _ hc hc
  have dist : Γ ⊢[PRAAx] crossEquivalent P B Z Y := distributive constantF L L c W W (constant_regular c) hl hl
  have half := GaussianStirlingDuplicationConstant.scale_half_double L W hl
  have addEq := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ dist) half
  have expEq := GaussianExponentialRadiusIndependence.independent_radii_proper B L (U B Y) (U L W) Y W
    (exponential_input _ _ hB) (exponential_input _ _ hl) addEq
  exact cross_trans _ _ _ _ _ _ (exponential_sum CF CF (CD x) (CD x) hc hc)
    (cross_trans _ _ _ _ _ _ expEq (GaussianStirlingDuplicationConstant.exponential_log_doubled_pi x))

theorem normalization_factors (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent denominatorF normalizationExpF (denominatorData a b x) (normalizationExpData a b x) := by
  let Q := normalizationSumF
  let Z := normalizationSumData a b x
  let X := point a b
  let N := negativeF constantF
  let V := negativeData X
  have hc := GaussianStirlingConstant.name_regular (Γ := Γ) x
  have hp := product_regular a b hs
  have hn := negative_fast constantF X (constant_regular (Γ := Γ) X)
  have hD := exponential_regular N V hn
  have hQ := normalization_sum_regular a b x hs
  have first := exponential_sum CF productF (CD x) (productData a b) hc hp
  have prod := multiply_cross firstFactorsF (E Q) decayF decayF (firstFactorsData a b x) (ed Q Z)
    (decayData a b) (decayData a b) (multiply_fast _ _ _ _ (sqrt_regular x) (exponential_regular _ _ hp))
    (exponential_regular _ _ hQ) hD hD first (cross_refl _ _ hD)
  exact cross_trans _ _ _ _ _ _ prod (exponential_sum Q N Z V hQ hn)

theorem cleared_formula (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF expRemainderF normalizationExpF) gammaF
      (multiplyData expRemainderF normalizationExpF (expRemainderData a b x) (normalizationExpData a b x)) (gammaData a b) := by
  let R := remainderData a b x
  let N := normalizationData a b x
  let G := logGammaData a b
  have hr := remainder_regular a b x hs
  have hn := normalization_regular a b x hs
  have hg := log_gamma_regular a b hs
  have first := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent remainderF normalizationF logGammaF
    (U remainderF R) (U normalizationF N) (U logGammaF G) R N G
    (exponential_input _ _ hr) (exponential_input _ _ hn) (exponential_input _ _ hg)
    (logarithmic_cancellation a b x hs)
  exact cross_trans _ _ _ _ _ _ first (exponential_gamma a b hs)

theorem normalization_inverse (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF normalizationExpF reciprocalF) oneF
      (multiplyData normalizationExpF reciprocalF (normalizationExpData a b x) (reciprocalData a b x))
      (normalizationData a b x) := by
  let N := normalizationData a b x
  let F := normalizationF
  let NF := negativeF F
  let X := negativeData N
  let R := U F N
  let S := U NF X
  have h := normalization_regular a b x hs
  have hn := negative_fast F N h
  have ih := exponential_input F N h
  have is := exponential_input NF X hn
  have ir := GaussianExponentialInverse.negative_input F R N ih
  have eq := GaussianExponentialRadiusIndependence.same_input_cross NF S R X is ir
  have first := multiply_cross normalizationExpF normalizationExpF reciprocalF reciprocalF
    (normalizationExpData a b x) (normalizationExpData a b x) (reciprocalData a b x) (GaussianRadiusExponentialName.data R X)
    (exponential_regular _ _ h) (exponential_regular _ _ h) (exponential_regular _ _ hn)
    (GaussianRadiusExponentialName.name_regular NF R X ir) (cross_refl _ _ (exponential_regular _ _ h)) eq
  exact cross_trans _ _ _ _ _ _ first (GaussianExponentialInverse.exponential_inverse F R N ih)

set_option maxHeartbeats 800000 in
theorem multiplicative_formula (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent expRemainderF quotientF (expRemainderData a b x) (quotientData a b x) := by
  let e := expRemainderData a b x
  let d := normalizationExpData a b x
  let k := reciprocalData a b x
  let o := normalizationData a b x
  let M := multiplyF normalizationExpF reciprocalF
  let m := multiplyData normalizationExpF reciprocalF d k
  let P := multiplyF expRemainderF normalizationExpF
  let p := multiplyData expRemainderF normalizationExpF e d
  have he := exponential_regular _ _ (remainder_regular a b x hs)
  have hn := normalization_regular a b x hs
  have hd := exponential_regular _ _ hn
  have hk := exponential_regular _ _ (negative_fast normalizationF o hn)
  have inv := cross_trans _ _ _ _ _ _ (normalization_inverse a b x hs)
    (GaussianBoundedInverseApartness.ones_equivalent o e)
  have z := multiply_cross expRemainderF expRemainderF M oneF e e m e he he
    (multiply_fast _ _ _ _ hd hk) (one_fast e) (cross_refl _ _ he) inv
  have first := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_one expRemainderF e he))
    (cross_symm _ _ _ _ z)
  have assoc := cross_symm _ _ _ _ (multiply_associative expRemainderF normalizationExpF reciprocalF e d k he hd hk)
  have last := multiply_cross P gammaF reciprocalF reciprocalF p (gammaData a b) k k
    (multiply_fast _ _ _ _ he hd) (gamma_regular a b hs) hk hk (cleared_formula a b x hs) (cross_refl _ _ hk)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc last)

theorem factor_inverse (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF denominatorF reciprocalF) oneF
      (multiplyData denominatorF reciprocalF (denominatorData a b x) (reciprocalData a b x))
      (normalizationData a b x) := by
  let d := denominatorData a b x
  let k := reciprocalData a b x
  have hn := normalization_regular a b x hs
  have hp := product_regular a b hs
  have hd := exponential_regular _ _ (negative_fast constantF (point a b) (constant_regular (Γ := Γ) _))
  have hk := exponential_regular _ _ (negative_fast normalizationF (normalizationData a b x) hn)
  have factorReg : Γ ⊢[PRAAx] pointCN denominatorF d :=
    multiply_fast _ _ _ _ (multiply_fast _ _ _ _ (sqrt_regular x) (exponential_regular _ _ hp)) hd
  have move := multiply_cross denominatorF normalizationExpF reciprocalF reciprocalF d (normalizationExpData a b x) k k
    factorReg (exponential_regular _ _ hn) hk hk (normalization_factors a b x hs) (cross_refl _ _ hk)
  exact cross_trans _ _ _ _ _ _ move (normalization_inverse a b x hs)

theorem actual_positive_rational_Stirling_multiplicative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ crossEquivalent expRemainderF quotientF
      (expRemainderData (var 0) (var 1) (var 2)) (quotientData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (multiplicative_formula _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicative
