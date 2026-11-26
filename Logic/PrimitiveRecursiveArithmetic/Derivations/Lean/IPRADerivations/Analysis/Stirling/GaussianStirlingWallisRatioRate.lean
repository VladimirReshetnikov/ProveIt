import IPRADerivations.Analysis.Stirling.GaussianStirlingWallisGammaRatio
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames
import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding

/-!
# Effective Wallis rate for the original Stirling half-step ratio

At (n=r+1), the original squared Gamma ratio approaches one with
finite error (3/n+3cdot 2^{-p}) at observation (p).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingWallisRatioRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingWallisGammaRatio (ratioF ratioData wallisF wallisData wallis_cross)
open GaussianStirlingWallisFactor (ratioFactor correction ratio_bound correction_distance ratio_times_wallis pair_odd_positive)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianGammaHalfWallisConvergence (twiceWallis original_Wallis_rate upperNumerator upperDenominator)
open GaussianGammaHalfWallisRate (evenSquare pairOdd odd)
open GaussianGammaHalfRisingFactorial (factorial_positive)
open GaussianStirlingNames (fraction_axis)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (multiply_at multiplyModulus product_distance)
open GaussianNameEquivalence (cross_at)
open GaussianRationalHorner (qmul qmul_canonical canonical_congr ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (qone)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalGaussianEmbedding (axis_congr canonical_axis_roundtrip)
open RationalValueBounds (upper upper_mono radius_of_upper)
open GaussianPositiveRationalLogarithm (fraction)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF

theorem pi_wallis_distance (p r x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 P p x) (twiceWallis (succ r))
      (upperNumerator (succ r) p) (upperDenominator (succ r) p) := by
  let N := succ r
  let U := unit p
  let F := fact (clearing p)
  let a := ap2 P p x
  let b := twiceWallis N
  let X := num 4*BaselQuadrature.Q (meshAt p) (clearing p)
  have hp := unit_positive (Γ := Γ) p
  have hb := pair_odd_positive (Γ := Γ) N
  have hF := factorial_positive (Γ := Γ) (clearing p)
  have den := positive_product (Γ := Γ) _ _ (zero_lt_succ r) hp
  have rA : Γ ⊢[PRAAx] a ≐ fraction X F := GaussianGammaHalfPiName.sample_at p x
  have eA := canonical_axis_roundtrip a (canonical_congr rA (ofGaussian_canonical _ _ hF))
    (axis_congr rA.eqSymm (fraction_axis X F hF))
  have eB := canonical_axis_roundtrip b (ofGaussian_canonical _ _ hb)
    (fraction_axis (two*evenSquare N) (pairOdd N) hb)
  have bounds := original_Wallis_rate (Γ := Γ) r p x
  have left : Γ ⊢[PRAAx] upper (fstT b) (fstT a) (upperNumerator N p) (upperDenominator N p) :=
    upper_mono _ _ _ _ _ _ hp bounds.andE₁ (by unfold upperNumerator upperDenominator; ipra_le 2*𝔞 U^2)
  exact distance_congr eA eB (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ den
      (radius_of_upper _ _ _ _ bounds.andE₂ left))

private theorem wallis_bound (N : PTm n) : Γ ⊢[PRAAx] bounded (twiceWallis N) (num 4) one :=
  GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (pair_odd_positive N)
    (le_congr (by unfold evenSquare; ipra_ring) (by unfold pairOdd; ipra_ring)
      (mul_le_mul_right two (WallisFinite.wallis_le_two N)))

theorem scaled_pi_distance (p r x : PTm n) : Γ ⊢[PRAAx] distanceBounded
    (qmul (ap2 P p x) (ratioFactor (succ r))) qone (num 3*unit p+succ r) (succ r*unit p) := by
  let N := succ r
  let U := unit p
  let a := ap2 P p x
  let b := twiceWallis N
  let c := ratioFactor N
  let w := qmul b c
  let R := upperNumerator N p
  have npos := zero_lt_succ (Γ := Γ) r
  have h := positive_product (Γ := Γ) N U npos (unit_positive p)
  have scaled := product_distance a b c c R zero (N*U) one (num 4) h
    (pi_wallis_distance p r x) (GaussianRationalPowerDifference.distance_refl_zero c _ h)
    (ratio_bound N) (wallis_bound N)
  have first : Γ ⊢[PRAAx] distanceBounded (qmul a c) w R (N*U) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) scaled
  have align : Γ ⊢[PRAAx] w ≐ correction N :=
    (GaussianRationalPowerAlgebra.qmul_commutative b c).eqTrans (ratio_times_wallis N)
  have second : Γ ⊢[PRAAx] distanceBounded w qone U (N*U) :=
    distance_radius_mono _ _ _ _ _ _ (zero_lt_succ _) h
      (by ipra_le 𝔞 U*(𝔞 N+1))
      (distance_congr align.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (correction_distance N))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [R,upperNumerator,N,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ h first second)

def wallisClock (p r x : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus P C x (ratioFactor (succ r))) p

theorem wallis_at (p r x : PTm n) : Γ ⊢[PRAAx] ap2 wallisF p (wallisData r x) ≐
    qmul (ap2 P (wallisClock p r x) x) (ratioFactor (succ r)) := by
  let q := wallisClock p r x
  let a := ap2 P q x
  let c := ratioFactor (succ r)
  let d := ap2 C q c
  have e := (multiply_at (Γ := Γ) P C x c p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul a d) (qmul_canonical a d))
  exact e.eqTrans (qmul_congr (.eqRefl _) (constant_at q c))

theorem wallis_rate (p r x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 wallisF p (wallisData r x)) qone (num 3*unit p+succ r) (succ r*unit p) := by
  let q := wallisClock p r x
  let N := succ r
  let U := unit p
  let V := unit q
  have grow : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right p _)
  have hn := zero_lt_succ (Γ := Γ) r
  exact distance_radius_mono _ _ (num 3*V+N) (N*V) (num 3*U+N) (N*U)
    (positive_product _ _ hn (unit_positive q)) (positive_product _ _ hn (unit_positive p))
    (by ipra_le 𝔞 N^2*sl grow)
    (distance_congr (wallis_at p r x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (scaled_pi_distance q r x))

theorem original_ratio_rate (p r x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 ratioF p (ratioData r)) qone (num 3*(unit p+succ r)) (succ r*unit p) := by
  let N := succ r
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product (Γ := Γ) N U (zero_lt_succ r) hp
  have e := cross_at (Γ := Γ) ratioF wallisF (ratioData r) (wallisData r x) p p (wallis_cross r x)
  have first := distance_radius_mono _ _ _ _ (two*N) (N*U) (positive_product _ _ hp hp) den (by ipra_le 0) e
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 wallisF p (wallisData r x)) qone (num 3*U+N) (N*U) := wallis_rate p r x
  have amount : Γ ⊢[PRAAx] two*N+(num 3*U+N) ≐ num 3*(U+N) := by ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) amount (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first second)

theorem actual_Stirling_original_Gamma_Wallis_ratio_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (distanceBounded (ap2 ratioF (var 2) (ratioData (var 1))) qone
      (num 3*(unit (var 2)+succ (var 1))) (succ (var 1)*unit (var 2))) :=
  closeUniv 3 (original_ratio_rate _ _ (var 0))

end LeanProofs.IPRA.Analysis.GaussianStirlingWallisRatioRate
