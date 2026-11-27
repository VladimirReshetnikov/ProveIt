import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationLogs
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRationalTelescopers
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingNames
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntervalLinearRemainder

/-!
# The vanishing residual in Stirling's duplication identity

The original positive rational log of (2a+b)/(2a) is compared to
b/(2a) through the actual harmonic mesh. Multiplication by a/b
gives an explicit b/(4a) bound on the residual, in addition to
the specified observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationResidual

open_ipra
open ComplexLogarithmRemainder (oneCode scale normSq)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (qadd qmul qzero positive_product ofGaussian_represents ofGaussian_canonical)
open GaussianRationalMetric (distanceBounded bounded qnegative qsub)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus addF addData add_fast sum_distance)
open GaussianNameRingLaws (three negativeF negativeData negative_fast add_sample_error negative_sample_error multiply_sample_error)
open GaussianStirlingNames (source)
open GaussianStirlingDuplicationLogs (halfRatioData)
open GaussianStirlingRationalTelescopers (fraction_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productF : PR 2 := multiplyF constantF logF
def productData (a b : PTm n) : PTm n := multiplyData constantF logF (fraction a b) (halfRatioData a b)
def nameF : PR 2 := addF constantF (negativeF productF)
def nameData (a b : PTm n) : PTm n := addData (fraction one two) (negativeData (productData a b))

theorem log_regular (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN logF (halfRatioData a b) := by
  have h : Γ ⊢[PRAAx] le one (two*a) := positive_product _ _ RationalAlgebra.two_positive ha
  exact GaussianPositiveRationalLogarithm.name_regular (two*a+b) (two*a) (.andI (le_trans h (le_add_right _ _)) h)

theorem name_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (nameData a b) :=
  add_fast _ _ _ _ (constant_regular _)
    (negative_fast _ _ (multiply_fast _ _ _ _ (constant_regular _) (log_regular a b hs.andE₁)))

private theorem fraction_bound_exact (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (fraction a b) a b := by
  apply GaussianRationalMetric.bounded_of_cleared _ (scale a oneCode) b a b hb hb (ofGaussian_represents _ _ hb)
  have norm : Γ ⊢[PRAAx] normSq (scale a oneCode) ≐ a*a :=
    (ComplexLogarithmRemainder.normSq_scale a oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact le_congr ((congrMul (.eqRefl (b*b)) norm).eqTrans (mul_comm (b*b) (a*a))).eqSymm
    (.eqRefl _) (le_refl ((a*a)*(b*b)))

private theorem centered_product (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qmul (fraction a b) (fraction b (two*a)) ≐ fraction one two := by
  have h := positive_product _ _ (RationalAlgebra.two_positive (Γ := Γ)) hs.andE₁
  exact (GaussianEulerDampedTimeRate.fraction_product a b b (two*a) hs.andE₂ h).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ hs.andE₂ h) RationalAlgebra.two_positive (by ipra_ring))

def observationBudget (a b : PTm n) : PTm n := multiplyModulus constantF logF (fraction a b) (halfRatioData a b)+num 7
def numerator (p a b : PTm n) : PTm n := b*b*unit p+num 4*a*(num 8*a+b*observationBudget a b)
def denominator (p a b : PTm n) : PTm n := num 4*a*b*unit p

theorem sample_bound (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b)) qzero (numerator p a b) (denominator p a b) := by
  let C := fraction a b
  let H : PTm n := fraction one two
  let L := halfRatioData a b
  let X := ap2 logF p L
  let Y := productData a b
  let M := multiplyModulus constantF logF C L
  let U := unit p
  let V := two*a
  have hp := unit_positive (Γ := Γ) p
  have hv := positive_product _ _ (RationalAlgebra.two_positive (Γ := Γ)) hs.andE₁
  have hvv := positive_product _ _ hv hv
  have hL := log_regular a b hs.andE₁
  have regularY := multiply_fast constantF logF C L (constant_regular C) hL
  have regularN := negative_fast productF Y regularY
  have e₁ := multiply_sample_error constantF logF C L p (constant_regular C) hL
  have e₂ := negative_sample_error productF Y p regularY
  have e₃ := add_sample_error constantF (negativeF productF) H (negativeData Y) p (constant_regular H) regularN
  have e₁' := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p C) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) e₁
  have nf := GaussianEulerExponentCompactBounds.negative_distance _ _ _ _ hp e₁'
  have base := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) qzero U hp
  have nq := distance_congr (.eqRefl _) (.eqRefl _) (zero_add _)
    (.eqRefl _) (sum_distance qzero qzero _ _ zero (M+one) U hp base nf)
  have neg : Γ ⊢[PRAAx] distanceBounded (ap2 (negativeF productF) p (negativeData Y))
      (qadd qzero (qnegative (qmul C X))) (three+(M+one)) U :=
    distance_triangle_same _ _ _ _ _ _ hp e₂ nq
  have e₃' := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr (constant_at p H) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) e₃
  have Hcan : Γ ⊢[PRAAx] GaussianRationalHorner.canonical H :=
    ofGaussian_canonical _ _ RationalAlgebra.two_positive
  have merge := (GaussianRationalSumAlgebra.qadd_associative (Γ := Γ) H qzero (qnegative (qmul C X))).eqSymm.eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (GaussianReciprocalHorner.qadd_zero_right H Hcan) (.eqRefl _))
  have carried : Γ ⊢[PRAAx] distanceBounded
      (qadd H (ap2 (negativeF productF) p (negativeData Y)))
      (qadd H (qadd qzero (qnegative (qmul C X)))) (zero+(three+(M+one))) U :=
    sum_distance H H (ap2 (negativeF productF) p (negativeData Y))
      (qadd qzero (qnegative (qmul C X))) zero (three+(M+one)) U hp
      (GaussianRationalPowerDifference.distance_refl_zero H U hp) neg
  have avg := distance_congr (.eqRefl _) merge (.eqRefl _) (.eqRefl _) carried
  have budgetEq : Γ ⊢[PRAAx] three+(zero+(three+(M+one))) ≐ observationBudget a b := by
    dsimp [observationBudget,M,C,L,three]
    ipra_ring
  have rounding := distance_congr (.eqRefl _) (.eqRefl _) budgetEq (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp e₃' avg)
  have obs := GaussianPositiveRationalLogarithmProperness.sample_interval_error p (V+b) V
    (.andI (le_trans hv (le_add_right V b)) hv)
  have approx := GaussianHarmonicIntervalLinearRemainder.interval_remainder V b (GammaEulerConstantName.mesh p) hv
    (GammaEulerConstantName.mesh_positive p)
  have logError := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hp hvv obs
    (distance_symmetric _ _ _ _ hvv approx)
  have scaled := bounded_product C (GaussianRationalMetric.qsub X (fraction b V)) a b _ (U*(V*V)) hs.andE₂
    (positive_product _ _ hp hvv) (fraction_bound_exact a b hs.andE₂) logError
  have center := bound_congr (GaussianRationalRoundedPower.multiplication_difference C X (fraction b V)).eqSymm
    (.eqRefl _) (.eqRefl _) scaled
  have center' := distance_congr (.eqRefl _) (centered_product a b hs) (.eqRefl _) (.eqRefl _) center
  have R : Γ ⊢[PRAAx] le one (denominator p a b) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (by ipra_le 3) hs.andE₁) hs.andE₂) hp
  have raw := distance_radius_mono _ _ _ _ (b*b*U+num 4*a*(num 8*a)) (denominator p a b)
    (positive_product _ _ hs.andE₂ (positive_product _ _ hp hvv)) R
    (le_of_eq_add (d := zero) (by dsimp [denominator,V,U]; ipra_ring)) center'
  have centerZero := (GaussianReconstructionRoots.distance_zero_iff (qsub H (qmul C X))
    (b*b*U+num 4*a*(num 8*a)) (denominator p a b) R).andE₂.impE
    (distance_symmetric _ _ _ _ R raw)
  have paid := distance_radius_mono _ _ _ _ (num 4*a*b*observationBudget a b) (denominator p a b) hp R
    (le_of_eq_add (d := zero) (by dsimp [denominator,U]; ipra_ring)) rounding
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp [numerator,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ R paid centerZero)

def uniformNumerator (p a b : PTm n) : PTm n := b*unit p+num 12*a
def uniformDenominator (p a : PTm n) : PTm n := num 4*a*unit p

theorem uniform_sample_bound (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b)) qzero
      (uniformNumerator p a b) (uniformDenominator p a) := by
  let Z := num 8*a+b*observationBudget a b
  let s := p+Z
  let U := unit p
  let V := unit s
  let A := num 4*a
  let D := uniformDenominator p a
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) s
  have hA : Γ ⊢[PRAAx] le one A := positive_product _ _ (by ipra_le 3) hs.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hA hU
  have hS : Γ ⊢[PRAAx] le one (denominator s a b) :=
    positive_product _ _ (positive_product _ _ hA hs.andE₂) hV
  have cover : Γ ⊢[PRAAx] le (Z*U) V :=
    le_congr (.eqRefl _) ((mul_comm (unit Z) U).eqTrans (pw_add two p Z).eqSymm)
      (mul_le_mul_right U (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self Z))
  have cap : Γ ⊢[PRAAx] le (Z*U) (b*V) := le_trans cover
    (le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hs.andE₂))
  have paid : Γ ⊢[PRAAx] distanceBounded (ap2 nameF s (nameData a b)) qzero (b*U+A) D := by
    apply distance_radius_mono _ _ _ _ _ _ hS hD ?_ (sample_bound s a b hs)
    change Γ ⊢[PRAAx] le ((b*b*V+num 4*a*Z)*(num 4*a*U)) ((b*U+num 4*a)*(num 4*a*b*V))
    ipra_le 16*(𝔞 a)^2*sl cap
  have clocks : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right p Z)
  have earlier : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b)) (ap2 nameF s (nameData a b)) (two*A) D := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) hD ?_
      (GaussianNameEquivalence.point_at nameF (nameData a b) p s (name_regular a b hs))
    change Γ ⊢[PRAAx] le ((U+V)*(A*U)) ((two*A)*(U*V))
    ipra_le (𝔞 A*𝔞 U)*sl clocks
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold uniformNumerator; dsimp [U,A]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD earlier paid)

theorem actual_stirling_duplication_residual_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶ distanceBounded (ap2 nameF (var 0) (nameData (var 1) (var 2))) qzero
      (uniformNumerator (var 0) (var 1) (var 2)) (uniformDenominator (var 0) (var 1))) :=
  closeUniv 3 (.impI (uniform_sample_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationResidual
