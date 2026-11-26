import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.GaussianBarnesCanonicalIntegerStirlingGamma
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherLimitName
import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantRationalRate
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedSumDifference

/-!
# The original integer Barnes logarithm and the leading asymptotic

The comparison uses the actual Stirling normalizer for the factorial
and the actual cofinal Glaisher logarithm for the hyperfactorial.
The leading error is bounded by `3/N^2` at every encoded integer
`N ≥ 2`, with independent dyadic observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerAsymptotic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalIntegerLogarithm (barnesLogData barnes_regular factorialLogData weightedF weightedData
  weighted_regular original_prefix_sum)
open GaussianBarnesGlaisherFinite (squareQuarter)
open GaussianBarnesGlaisherQuartic (negativeWeight)
open GaussianBarnesGlaisherInterval (square square_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRationalWendelBoundary (difference_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedDifference (name_regular)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingGammaLogarithm (logGammaF log_gamma_regular)
open GaussianStirlingCubicCell (cube cube_positive)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "S" => GaussianBarnesGlaisherFinite.sumF
local notation "sd" => GaussianBarnesGlaisherFinite.sumData
local notation "W" => GaussianBarnesGlaisherFinite.weightedF
local notation "w" => GaussianBarnesGlaisherFinite.weightedData
local notation "A" => GaussianBarnesGlaisherFinite.nameF
local notation "ad" => GaussianBarnesGlaisherFinite.data
local notation "T" => GaussianBarnesGlaisherLimitName.nameF
local notation "td" => GaussianBarnesGlaisherLimitName.data
local notation "F" => GaussianBarnesCanonicalIntegerStirlingGamma.approximationF
local notation "fd" => GaussianBarnesCanonicalIntegerStirlingGamma.approximationData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def logarithmicWeight (N : PTm n) : PTm n := w (negativeWeight N) N

abbrev recoveredPrefixF : PR 2 := Diff (Diff A constantF) W
def recoveredPrefixData (N : PTm n) : PTm n := dd (dd (ad N) (squareQuarter N)) (logarithmicWeight N)
abbrev approximatePrefixF : PR 2 := Diff (Diff T constantF) W
def approximatePrefixData (N : PTm n) : PTm n := dd (dd td (squareQuarter N)) (logarithmicWeight N)

abbrev approximateWeightedFactorialF : PR 2 := productF F
def approximateWeightedFactorialData (N : PTm n) : PTm n := productData F N (fd N)

abbrev approximationF : PR 2 := Diff approximateWeightedFactorialF approximatePrefixF
def approximationData (N : PTm n) : PTm n := dd (approximateWeightedFactorialData N) (approximatePrefixData N)

private theorem subtract_right (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (Diff (addF f g) g) f (dd (addData x y) y) x := by
  have commuting := GaussianNameRingLaws.add_commutative f g x y hf hg
  have diff := difference_cross (addF f g) (addF g f) g g (addData x y) (addData y x) y y
    (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hg hf) hg hg commuting (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ diff (GaussianNamedSumDifference.cancel_added g f y x hg hf)

theorem recovered_prefix (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent recoveredPrefixF S (recoveredPrefixData N) (sd N) := by
  let x := sd N
  let y := logarithmicWeight N
  let z := squareQuarter N
  have hx := GaussianBarnesGlaisherFinite.sum_regular (Γ := Γ) N
  have hy := GaussianBarnesGlaisherFinite.weighted_regular (negativeWeight N) N hN
  have hz := constant_regular (Γ := Γ) z
  have joined := add_fast _ _ _ _ hx hy
  have first := subtract_right (addF S W) constantF (addData x y) z joined hz
  have carry := difference_cross (Diff A constantF) (addF S W) W W (dd (ad N) z) (addData x y) y y
    (name_regular _ _ _ _ (GaussianBarnesGlaisherFinite.regular N hN) hz) joined hy hy
    first (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _ carry (subtract_right S W x y hx hy)

theorem approximate_prefix_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN approximatePrefixF (approximatePrefixData N) :=
  name_regular _ _ _ _ (name_regular _ _ _ _ GaussianBarnesGlaisherLimitName.regular (constant_regular _))
    (GaussianBarnesGlaisherFinite.weighted_regular _ _ hN)

theorem prefix_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate S approximatePrefixF (sd N) (approximatePrefixData N) two (square N) := by
  let D := square N
  let q := squareQuarter N
  let y := logarithmicWeight N
  have h1 := le_trans (le_succ_self one) hN
  have hd := square_positive N h1
  have ha := GaussianBarnesGlaisherFinite.regular N h1
  have ht := GaussianBarnesGlaisherLimitName.regular (Γ := Γ) (n := n)
  have hq := constant_regular (Γ := Γ) q
  have hw := GaussianBarnesGlaisherFinite.weighted_regular (negativeWeight N) N h1
  have first := GaussianNamedRateComposition.symmetric T A td (ad N) two D hd
    (GaussianBarnesGlaisherLimitName.finite_limit_rate N hN)
  have step := GaussianNamedDifferenceRate.same_right_rate A T constantF (ad N) td q two D hd ha ht hq first
  have fin := GaussianNamedDifferenceRate.same_right_rate (Diff A constantF) (Diff T constantF) W
    (dd (ad N) q) (dd td q) y two D hd (name_regular _ _ _ _ ha hq) (name_regular _ _ _ _ ht hq) hw step
  exact GaussianNamedRateTransport.transport recoveredPrefixF approximatePrefixF S approximatePrefixF
    (recoveredPrefixData N) (approximatePrefixData N) (sd N) (approximatePrefixData N) two D hd fin
    (cross_symm _ _ _ _ (recovered_prefix N h1)) (cross_refl _ _ (approximate_prefix_regular N h1))

theorem approximate_weighted_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN approximateWeightedFactorialF (approximateWeightedFactorialData N) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianBarnesCanonicalIntegerStirlingGamma.approximation_regular N hN)

theorem weighted_factorial_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate weightedF approximateWeightedFactorialF (weightedData N)
      (approximateWeightedFactorialData N) one (square N) := by
  let G := logGammaF
  let x := factorialLogData N
  let y := fd N
  let a := naturalPoint N
  let B := cube N
  let D := square N
  let P := GaussianBoundedConstantProductName.nameF
  let pd := GaussianBoundedConstantProductName.data (n := n)
  have hx := log_gamma_regular _ _ (GaussianBarnesCanonicalIntegerLogarithm.factorial_source (Γ := Γ) N)
  have hy := GaussianBarnesCanonicalIntegerStirlingGamma.approximation_regular N hN
  have ha := GaussianNamedNaturalScale.natural_point_bound (Γ := Γ) N
  have hB := cube_positive N hN
  have hD := square_positive N hN
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  have budget : Γ ⊢[PRAAx] le N (N*one) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  have raw := GaussianBoundedConstantRationalRate.original_rate G F N a x y N one one B h1 hB budget ha
    (GaussianBarnesCanonicalIntegerStirlingGamma.factorial_logarithm_rate N hN)
  have narrowing := GaussianNamedRateRadius.weaken (P G) (P F) (pd N a x) (pd N a y)
    (N*one) (one*B) one D (positive_product _ _ h1 hB) hD
    (le_of_eq_add (d := zero) (by unfold D B cube square; ipra_ring)) raw
  have left := GaussianBoundedConstantProductName.ordinary_product_identity G N a x (.andI hx ha)
  have right := GaussianBoundedConstantProductName.ordinary_product_identity F N a y (.andI hy ha)
  exact GaussianNamedRateTransport.transport (P G) (P F) weightedF approximateWeightedFactorialF (pd N a x) (pd N a y)
    (weightedData N) (approximateWeightedFactorialData N) one D hD narrowing
    (cross_symm _ _ _ _ left) (cross_symm _ _ _ _ right)

theorem approximation_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN approximationF (approximationData N) :=
  name_regular _ _ _ _ (approximate_weighted_regular N hN) (approximate_prefix_regular N hN)

theorem integer_asymptotic_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate L approximationF (barnesLogData N) (approximationData N) (num 3) (square N) := by
  let D := square N
  let u := weightedData N
  let v := sd N
  let x := approximateWeightedFactorialData N
  let y := approximatePrefixData N
  let z := barnesLogData N
  let F' := Diff weightedF S
  let K := GaussianBarnesCanonicalIntegerLogarithm.prefixSumF
  let k := GaussianBarnesCanonicalIntegerLogarithm.prefixSumData N
  have h1 := le_trans (le_succ_self one) hN
  have hd := square_positive N h1
  have hu := weighted_regular (Γ := Γ) N
  have hv := GaussianBarnesGlaisherFinite.sum_regular (Γ := Γ) N
  have hx := approximate_weighted_regular N h1
  have hy := approximate_prefix_regular N h1
  have hz := barnes_regular (Γ := Γ) N
  have hs := GaussianNamedDifferenceRate.original_rate weightedF S approximateWeightedFactorialF approximatePrefixF
    u v x y one D two D (.andI (.andI hd hd) (.andI (.andI hu hv) (.andI (.andI hx hy)
      (.andI (weighted_factorial_rate N h1) (prefix_rate N hN)))))
  have norm := GaussianNamedRateRadius.weaken F' approximationF (dd u v) (approximationData N)
    (GaussianNamedDifferenceRate.leadingNumerator one D two D) (GaussianNamedDifferenceRate.leadingDenominator D D)
    (num 3) D (positive_product _ _ hd hd) hd
    (le_of_eq_add (d := zero) (by unfold GaussianNamedDifferenceRate.leadingNumerator GaussianNamedDifferenceRate.leadingDenominator; ipra_ring))
    hs
  have rel := difference_cross K weightedF S S k u v v (add_fast _ _ _ _ hz hv) hu hv hv
    (original_prefix_sum N) (cross_refl _ _ hv)
  have eq := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (subtract_right L S z v hz hv)) rel
  exact GaussianNamedRateTransport.transport F' approximationF L approximationF (dd u v) (approximationData N)
    z (approximationData N) (num 3) D hd norm eq (cross_refl _ _ (approximation_regular N h1))

theorem actual_original_Barnes_integer_asymptotic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ independentRate L approximationF (barnesLogData (var 0))
      (approximationData (var 0)) (num 3) (square (var 0))) :=
  closeUniv 1 (.impI (integer_asymptotic_rate _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerAsymptotic
