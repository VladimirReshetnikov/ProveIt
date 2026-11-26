import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveLogarithmRealAxis
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorialIntegers
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalGaussNormalizers
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherHyperfactorial

/-!
# Exact logarithmic superfactorial at original Barnes integer inputs

The original positive Barnes logarithm and the actual finite weighted
hyperfactorial logarithms sum to the original factorial logarithm
multiplied by the same integer. Equality follows from the exact encoded
product identity and injectivity of the actual real exponential names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerLogarithm

open_ipra
open BarnesInteger (barnes hyp hyper_cross)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (logF baseF)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical canonical_unique)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents natScale_as_product)
open GaussianRationalReciprocal (power power_canonical)
open GaussianRealNameExponentialInjectivity (axisSamples axis_sample_at independent_radii_injective)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular log_gamma_axis)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "Gd" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "V" => GaussianBarnesCanonicalValue.nameF

def barnesRadius (N : PTm n) : PTm n := succ N+one
def barnesLogData (N : PTm n) : PTm n := Gd (succ N) one (barnesRadius N)
def factorialLogData (N : PTm n) : PTm n := logGammaData (succ N) one
def hyperLogData (N : PTm n) : PTm n := GaussianPositiveRationalLogarithm.data (hyp N) one
abbrev weightedF : PR 2 := productF logGammaF
def weightedData (N : PTm n) : PTm n := productData logGammaF N (factorialLogData N)
abbrev exactSumF : PR 2 := addF G logF
def exactSumData (N : PTm n) : PTm n := addData (barnesLogData N) (hyperLogData N)
abbrev prefixSumF : PR 2 := addF G GaussianBarnesGlaisherFinite.sumF
def prefixSumData (N : PTm n) : PTm n := addData (barnesLogData N) (GaussianBarnesGlaisherFinite.sumData N)

theorem barnes_source (N : PTm n) : Γ ⊢[PRAAx]
    GaussianBarnesCanonicalPositiveLogarithm.source (succ N) one (barnesRadius N) :=
  GaussianBarnesCanonicalPositiveLogarithm.default_source (succ N) one (zero_lt_succ N) (le_refl one)

theorem barnes_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN G (barnesLogData N) :=
  GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ (barnes_source N)

theorem factorial_source (N : PTm n) : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (succ N) one :=
  .andI (zero_lt_succ _) (le_refl _)

theorem weighted_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN weightedF (weightedData N) :=
  multiply_fast _ _ _ _ (constant_regular _) (log_gamma_regular _ _ (factorial_source N))

theorem hyper_source (N : PTm n) : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (hyp N) one :=
  .andI (GaussianBarnesGlaisherHyperfactorial.hyp_positive N) (le_refl one)

private theorem center_at_integer (N : PTm n) :
    Γ ⊢[PRAAx] equal (GaussianBarnesCanonicalThirdLogarithmRows.center (succ N) one) (scale N oneCode) := by
  apply equal_of_values <;>
    simp only [GaussianBarnesCanonicalThirdLogarithmRows.center,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem original_exponential_barnes (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (E G) constantF (exponentialInputData G (barnesLogData N)) (naturalPoint (barnes N)) := by
  let z := GaussianBarnesCanonicalThirdLogarithmRows.center (succ N) one
  let w := scale N oneCode
  let R := barnesRadius N
  let h := barnes_source (Γ := Γ) N
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have src : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source w N one :=
    .andI h1 (le_congr ((ComplexLogarithmRemainder.normSq_scale N oneCode).eqTrans
      (congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one)).eqSymm (by ipra_ring) (le_refl (N*N*one)))
  have eq := GaussianGammaFiniteValueProperness.fraction_equal z w one h1 (center_at_integer N)
  have direct := GaussianBarnesCanonicalPositiveLogarithm.exponential_value (succ N) one R h
  have move := GaussianBarnesCanonicalProperness.proper z w R N one one h.andE₂ src eq
  exact cross_trans _ _ _ _ _ _ direct
    (cross_trans _ _ _ _ _ _ move (GaussianBarnesCanonicalIntegerValues.original_integer_value N))

theorem original_exponential_weighted_factorial (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (E weightedF) constantF (exponentialInputData weightedF (weightedData N))
      (naturalPoint (pw (fact N) N)) := by
  let L := logGammaF
  let x := factorialLogData N
  let y := weightedData N
  let R := U L x
  let Q := GaussianNamedNaturalScale.radius N R
  let S := GaussianNamedNaturalScale.nameF L
  let s := GaussianNamedNaturalScale.data N N x
  let c := naturalPoint (fact N)
  have hx := log_gamma_regular (succ N) one (factorial_source (Γ := Γ) N)
  have hi := exponential_input L x hx
  have hy := weighted_regular (Γ := Γ) N
  have scale_cross := GaussianNaturalScaleProductName.scale_product_cross L N N R x hi (le_refl N)
  have expCross := GaussianExponentialRadiusIndependence.independent_radii_proper weightedF S
    (U weightedF y) Q y s (exponential_input _ _ hy)
    (GaussianNamedNaturalScale.exponential_input L N N R x hi (le_refl N))
    (cross_symm _ _ _ _ scale_cross)
  have base : Γ ⊢[PRAAx] GaussianBoundedIntegerExponentialStages.input L R x c (fact N) :=
    .andI hi (.andI (GaussianBarnesCanonicalGaussNormalizers.factorial_log_exponential N)
      (GaussianNamedNaturalScale.natural_point_bound (fact N)))
  have powered := GaussianBoundedIntegerExponential.integer_power_cross L N R x c (fact N) base
  have literal : Γ ⊢[PRAAx] power c N ≐ naturalPoint (pw (fact N) N) :=
    canonical_unique _ _ _ one (power_canonical _ _) (ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
      (GaussianExponentialDiskMajorant.natural_power_represents (fact N) N) (natural_point_represents _)
  exact cross_trans _ _ _ _ _ _ expCross (cross_trans _ _ _ _ _ _ powered
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ literal))

theorem weighted_axis (N : PTm n) : Γ ⊢[PRAAx] axisSamples weightedF (weightedData N) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let N' := Syn.shift N
  let x := factorialLogData N'
  let p : PTm (n+1) := var 0
  let t := GaussianNaturalScaleProductName.clock logGammaF p N' x
  have raw := (GaussianNaturalScaleProductName.product_at (Γ := Δ) logGammaF p N' x).eqTrans
    (natScale_as_product N' (ap2 logGammaF t x))
  have ha := RationalGaussianEmbedding.axis_multiply (Γ := Δ) (naturalPoint N') (ap2 logGammaF t x)
    (GaussianStirlingNames.fraction_axis N' one (le_refl one))
    (axis_sample_at logGammaF x t (log_gamma_axis (succ N') one))
  simpa [axisSamples,Syn.shift,weightedData,factorialLogData,Δ,N',x,p,GaussianNaturalScaleProductName.sample]
    using RationalGaussianEmbedding.axis_congr raw.eqSymm ha

theorem exact_sum (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent exactSumF weightedF (exactSumData N) (weightedData N) := by
  let a := barnesLogData N
  let b := hyperLogData N
  let x := exactSumData N
  let y := weightedData N
  let u := exponentialInputData G a
  let v := exponentialInputData logF b
  let k := multiplyData (E G) (E logF) u v
  let c := naturalPoint (barnes N)
  let d := naturalPoint (hyp N)
  let e := naturalPoint (pw (fact N) N)
  have ha := barnes_regular (Γ := Γ) N
  have hb := GaussianPositiveRationalLogarithm.name_regular (hyp N) one (hyper_source (Γ := Γ) N)
  have hx := add_fast G logF a b ha hb
  have hy := weighted_regular (Γ := Γ) N
  have ia := exponential_input G a ha
  have ib := exponential_input logF b hb
  have ix := exponential_input exactSumF x hx
  have iy := exponential_input weightedF y hy
  have split := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent G logF exactSumF
    (U G a) (U logF b) (U exactSumF x) a b x ia ib ix (cross_refl _ _ hx)
  have prod := GaussianGammaAdjacentCutoff.multiply_cross (E G) constantF (E logF) constantF u c v d
    (GaussianRadiusExponentialName.name_regular _ _ _ ia) (constant_regular c)
    (GaussianRadiusExponentialName.name_regular _ _ _ ib) (constant_regular d)
    (original_exponential_barnes N) (GaussianPositiveRationalLogarithm.exponential_fraction (hyp N) one (hyper_source N))
  have arithmetic : Γ ⊢[PRAAx] GaussianRationalHorner.qmul c d ≐ e :=
    (GaussianGammaFactorialValues.natural_product (barnes N) (hyp N)).eqTrans
      (GaussianGammaFactorialValues.natural_congr (hyper_cross N))
  have values := GaussianGammaDigammaTwoShiftNamedSize.constant_product c d e arithmetic
  have exp := cross_trans (E exactSumF) (multiplyF (E G) (E logF)) (E weightedF)
    (exponentialInputData exactSumF x) k (exponentialInputData weightedF y) (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ prod (cross_trans _ _ _ _ _ _ values
      (cross_symm _ _ _ _ (original_exponential_weighted_factorial N))))
  have axes := GaussianNamedPositiveLogarithmScale.sum_axis (Γ := Γ) G logF a b
    (GaussianBarnesCanonicalPositiveLogarithmRealAxis.samples_axis _ _ _ (barnes_source N))
    (GaussianNamedPositiveLogarithmScale.exact_rational_axis (hyp N) one)
  exact independent_radii_injective exactSumF weightedF _ _ x y ix iy axes (weighted_axis N) exp

theorem original_prefix_sum (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent prefixSumF weightedF (prefixSumData N) (weightedData N) := by
  let S := GaussianBarnesGlaisherFinite.sumF
  let s := GaussianBarnesGlaisherFinite.sumData N
  let a := barnesLogData N
  let b := hyperLogData N
  have hs := GaussianBarnesGlaisherHyperfactorial.hyp_positive (Γ := Γ) N
  have pref := cross_trans S baseF logF s (hyp N) b
    (GaussianBarnesGlaisherHyperfactorial.prefix_hyperfactorial_logarithm N)
    (cross_symm _ _ _ _ (GaussianBetaUpperPowerCancellation.rational_log_integer (hyp N) hs))
  have hg := barnes_regular (Γ := Γ) N
  have sums := GaussianNamedGammaHalfShift.add_cross G G S logF a a s b hg hg
    (GaussianBarnesGlaisherFinite.sum_regular N) (GaussianPositiveRationalLogarithm.name_regular _ _ (hyper_source N))
    (cross_refl _ _ hg) pref
  exact cross_trans _ _ _ _ _ _ sums (exact_sum N)

theorem actual_original_Barnes_integer_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent prefixSumF weightedF (prefixSumData (var 0)) (weightedData (var 0))) :=
  closeUniv 1 (original_prefix_sum _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerLogarithm
