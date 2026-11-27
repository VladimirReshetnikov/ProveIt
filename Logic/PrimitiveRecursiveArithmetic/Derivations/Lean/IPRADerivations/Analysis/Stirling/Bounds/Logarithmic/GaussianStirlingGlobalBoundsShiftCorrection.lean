import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBoundsShiftArguments
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntervalLinearRemainder
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationResidual

/-!
# The elementary fractional-shift correction in Stirling's remainder

At (u=r/bin(0,1]), the harmonic logarithm of (1+u/i) differs from
(u/i) by at most ((u/i)^2) before observation errors. Applying the
literal coefficient and subtracting from (u) gives an error of order
(1/i) for the actual named arithmetic.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsShiftCorrection

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero qmul positive_product ofGaussian_represents represents represents_congr represents_rescale
  canonical_unique qmul_canonical qmul_represents)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_represents qsub_canonical)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum bounded_negative)
open GaussianRationalSyntheticDivision (qmul_congr rescale_to)
open GaussianRationalPowerDifference (distance_refl_zero bounded_sum_one)
open GaussianRootAlgebra (equal equal_of_values sub re_sub im_sub re_mul im_mul re_scale im_scale re_one im_one)
open GaussianStirlingGlobalBoundsShiftArguments (shiftedNumerator positiveFraction ratioData shifted_positive log_ratio_regular)
open GaussianStirlingNames (offset point)
open GaussianPositiveRationalLogarithm (fraction logF)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def productF : PR 2 := multiplyF constantF logF
def productData (i r b : PTm n) : PTm n :=
  multiplyData constantF logF (offset (shiftedNumerator i r b) b) (ratioData i r b)
def correctionF : PR 2 := GaussianNamedDifference.nameF constantF productF
def correctionData (i r b : PTm n) : PTm n := GaussianNamedDifference.data (positiveFraction r b) (productData i r b)
def budget (i r b : PTm n) : PTm n :=
  (multiplyModulus constantF logF (offset (shiftedNumerator i r b) b) (ratioData i r b)+num 7)+num 8*(i+two)

ipra_subst productData
ipra_subst correctionData [positiveFraction]
ipra_subst budget [GaussianNameArithmetic.multiplyModulus]

theorem product_regular (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN productF (productData i r b) :=
  multiply_fast _ _ _ _ (constant_regular _) (log_ratio_regular i r b hi hb)

theorem correction_regular (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN correctionF (correctionData i r b) :=
  GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (product_regular i r b hi hb)

theorem point_at_double_scale (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (point a b) (scale two (scale a oneCode)) (two*b) :=
  rescale_to _ _ b two (two*b) (ofGaussian_represents _ _ hb) (mul_comm _ _)

theorem offset_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (offset a b) (sub (scale two (scale a oneCode)) (scale b (scale one oneCode))) (two*b) :=
  qsub_represents _ _ _ _ _ (positive_product _ _ RationalAlgebra.two_positive hb) (point_at_double_scale a b hb)
    (represents_rescale _ _ two b (ofGaussian_represents _ _ RationalAlgebra.two_positive))

private theorem fraction_bound (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (fraction a b) a b :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded a b hb)

private theorem coefficient_bound (i r b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] bounded (offset (shiftedNumerator i r b) b) (i+two) one := by
  let z := shiftedNumerator i r b
  let h : PTm n := fraction one two
  have cle : Γ ⊢[PRAAx] le (z*one) ((i+one)*b) := by dsimp [z,shiftedNumerator]; ipra_le sl hr
  have c := bounded_radius_mono _ _ _ _ _ hb (le_refl one) cle (fraction_bound z b hb)
  have H : Γ ⊢[PRAAx] bounded h one one := bounded_radius_mono h one two one one RationalAlgebra.two_positive (le_refl one) (by ipra_le 1)
    (fraction_bound one two RationalAlgebra.two_positive)
  have sum := bounded_sum_one c (bounded_negative _ _ _ (le_refl one) H)
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) sum

private theorem centered_identity (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub (positiveFraction r b) (qmul (offset (shiftedNumerator i r b) b) (fraction r (b*i))) ≐
      qmul (qsub (fraction one two) (positiveFraction r b)) (fraction r (b*i)) := by
  let z := shiftedNumerator i r b
  let u := positiveFraction r b
  let H : PTm n := fraction one two
  let t := fraction r (b*i)
  let C := two*b
  let V := b*i
  let E := C*V
  let j := scale r oneCode
  let h := scale b (scale one oneCode)
  let c := sub (scale two (scale z oneCode)) h
  let d := sub h (scale two j)
  have hc := positive_product (Γ := Γ) two b RationalAlgebra.two_positive hb
  have hv := positive_product (Γ := Γ) b i hb hi
  have he := positive_product _ _ hc hv
  have hu : Γ ⊢[PRAAx] represents u (scale (two*V) j) E :=
    rescale_to _ _ b (two*V) E (ofGaussian_represents _ _ hb) (by dsimp [E,V,C]; ipra_ring)
  have ht := ofGaussian_represents (Γ := Γ) j V hv
  have prod := qmul_represents (offset z b) t c j C V hc hv (offset_represents z b hb) ht
  have hd := qsub_represents H u _ _ C hc (represents_rescale _ _ two b (ofGaussian_represents _ _ RationalAlgebra.two_positive))
    (point_at_double_scale r b hb)
  have rhs := qmul_represents (qsub H u) t d j C V hc hv hd ht
  have lhs := qsub_represents u (qmul (offset z b) t) _ _ E he hu prod
  apply canonical_unique _ _ _ E (qsub_canonical _ _) (qmul_canonical _ _) he (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;>
    simp only [c,d,h,j,z,shiftedNumerator,V,re_sub,im_sub,re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

private theorem centered_bound (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] bounded (qsub (positiveFraction r b) (qmul (offset (shiftedNumerator i r b) b) (fraction r (b*i)))) two i := by
  let H : PTm n := fraction one two
  let u := positiveFraction r b
  let t := fraction r (b*i)
  have hu := bounded_radius_mono u r b one one hb (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hr) (fraction_bound r b hb)
  have hH : Γ ⊢[PRAAx] bounded H one one := bounded_radius_mono H one two one one RationalAlgebra.two_positive (le_refl one) (by ipra_le 1)
    (fraction_bound one two RationalAlgebra.two_positive)
  have ht := bounded_radius_mono t r (b*i) one i (positive_product _ _ hb hi) hi
    (by ipra_le 𝔞 i*sl hr) (fraction_bound r (b*i) (positive_product _ _ hb hi))
  have hC : Γ ⊢[PRAAx] bounded (qsub H u) two one :=
    bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) (bounded_sum_one hH
      (bounded_negative _ _ _ (le_refl one) hu))
  exact bound_congr (centered_identity i r b hi hb).eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) hi hC ht)

theorem sample_bound (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 correctionF p (correctionData i r b)) qzero
      (num 5*unit p+i*budget i r b) (i*unit p) := by
  let D := productData i r b
  let c := offset (shiftedNumerator i r b) b
  let u := positiveFraction r b
  let L := ratioData i r b
  let z := ap2 logF p L
  let M := multiplyModulus constantF logF c L
  let V := b*i
  let X := shiftedNumerator i r b
  let T := fraction r V
  let U := unit p
  let H := i+two
  let A := i*i
  have hp := unit_positive (Γ := Γ) p
  have ha := positive_product _ _ hi hi
  have hv := positive_product _ _ hb hi
  have hvv := positive_product _ _ hv hv
  have hd := positive_product _ _ hi hp
  have hA := positive_product _ _ ha hp
  have hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source X V := .andI (shifted_positive i r b hi hb) hv
  have q := GaussianNamedDifference.sample_error constantF productF u D p (constant_regular u)
    (product_regular i r b hi hb)
  have v := multiply_sample_error constantF logF c L p (constant_regular c) (log_ratio_regular i r b hi hb)
  have v' := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _) v
  have pu : Γ ⊢[PRAAx] distanceBounded (ap2 constantF p u) u zero U :=
    distance_congr (constant_at p u).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (distance_refl_zero u U hp)
  have r0 := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp pu v'
  have round : Γ ⊢[PRAAx] distanceBounded (ap2 correctionF p (correctionData i r b)) (qsub u (qmul c z)) (M+num 7) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hp q r0)
  have orig := GaussianPositiveRationalLogarithmProperness.sample_interval_error p X V hs
  have lin := GaussianHarmonicIntervalLinearRemainder.interval_remainder V r (GammaEulerConstantName.mesh p) hv
    (GammaEulerConstantName.mesh_positive p)
  have logErr := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hp hvv orig
    (distance_symmetric _ _ _ _ hvv lin)
  have cap : Γ ⊢[PRAAx] le (r*r*A) (V*V) := by
    have h := sq_le_sq (Γ := Γ) hr
    dsimp [A,V]
    ipra_le (𝔞 i)^2*sl h
  have leLog : Γ ⊢[PRAAx] distanceBounded z T (U+num 8*A) (A*U) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hvv) hA (by
      dsimp [U,A,V] at cap ⊢
      ipra_le (𝔞 (unit p))^2*sl cap) logErr
  have m := bounded_product c (qsub z T) H one (U+num 8*A) (A*U) (le_refl one) hA
    (coefficient_bound i r b hb hr) leLog
  have mid : Γ ⊢[PRAAx] distanceBounded (qmul c z) (qmul c T) (H*(U+num 8*A)) (A*U) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference c z T).eqSymm
      (.eqRefl _) (by ipra_ring) m
  have gap := GaussianNamedDifference.difference_distance u u (qmul c z) (qmul c T) zero _ _ hA
    (distance_refl_zero u _ hA) mid
  have hGap : Γ ⊢[PRAAx] distanceBounded (qsub u (qmul c z)) (qsub u (qmul c T)) (num 3*U+i*(num 8*H)) (i*U) := by
    apply distance_radius_mono _ _ _ _ _ _ hA hd ?_ gap
    dsimp only [A,H]
    ipra_le 2*𝔞 i*(𝔞 U)^2*sl hi
  let Z := qsub u (qmul c T)
  have cent : Γ ⊢[PRAAx] distanceBounded Z qzero two i :=
    bound_congr (GaussianRationalReconstruction.qsub_zero_right Z (qsub_canonical _ _)).eqSymm
      (.eqRefl _) (.eqRefl _) (centered_bound i r b hi hb hr)
  have cen : Γ ⊢[PRAAx] distanceBounded Z qzero (two*U) (i*U) :=
    distance_radius_mono _ _ _ _ _ _ hi hd (le_of_eq_add (d := zero) (by ipra_ring)) cent
  have er : Γ ⊢[PRAAx] distanceBounded (ap2 correctionF p (correctionData i r b)) (qsub u (qmul c z)) (i*(M+num 7)) (i*U) :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by ipra_ring)) round
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp [budget,M,H,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd er hGap) cen)

theorem uniform_sample_bound (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le r b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 correctionF p (correctionData i r b)) qzero (num 5*unit p+num 3*i) (i*unit p) := by
  let Z := budget i r b
  let s := p+Z
  let U := unit p
  let V := unit s
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) s
  have hp := positive_product _ _ hi hU
  have hs := positive_product _ _ hi hV
  have cover : Γ ⊢[PRAAx] le (Z*U) V :=
    le_congr (.eqRefl _) ((mul_comm (unit Z) U).eqTrans (pw_add two p Z).eqSymm)
      (mul_le_mul_right U (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self Z))
  have later := sample_bound i r b s hi hb hr
  have pay : Γ ⊢[PRAAx] distanceBounded (ap2 correctionF s (correctionData i r b)) qzero (num 5*U+i) (i*U) :=
    distance_radius_mono _ _ _ _ _ _ hs hp (by dsimp only [Z] at cover; ipra_le (𝔞 i)^2*sl cover) later
  have order : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right p Z)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 correctionF p (correctionData i r b))
      (ap2 correctionF s (correctionData i r b)) (two*i) (i*U) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) hp
      (by ipra_le (𝔞 i*𝔞 U)*sl order)
      (GaussianNameEquivalence.point_at _ _ p s (correction_regular i r b hi hb))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp near pay)

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsShiftCorrection
