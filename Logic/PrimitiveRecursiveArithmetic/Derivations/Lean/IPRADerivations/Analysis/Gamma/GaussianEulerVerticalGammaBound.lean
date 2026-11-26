import IPRADerivations.Analysis.Euler.GaussianEulerVerticalQuadrature
import IPRADerivations.Analysis.Euler.GaussianEulerVerticalShiftedRadius
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralPositiveLower
import IPRADerivations.Core.CertificateTactics

/-!
# Vertical norm domination for the original Gamma observations

For independent Gamma queries, the comparison radius is the real
coordinate of the original Gamma observation at the real part, plus
the two requested tolerances. The independent observation of the
improper integral adds a temporary error that a finite gap removes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalGammaBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerVerticalQuadrature (cutoffRadius cutoff_radius_budget)
open GaussianEulerVerticalRealRadius (gap denominator denominator_positive)
open GaussianEulerIntegralGammaIdentification (source original_Euler_integral_is_Gamma)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open RationalGaussianEmbedding (scalarZero)
open RationalValueBounds (upper upper_congr upper_of_radius upper_mono upper_triangle)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (p z R B A : PTm n) : PTm n := ap2 gammaF p (gammaData z R B A)
def radiusNumerator (p q z R B A : PTm n) : PTm n :=
  gap (point q (argument z) R B A) (unit q)*unit p+denominator (point q (argument z) R B A) (unit q)
def radiusDenominator (p q z R B A : PTm n) : PTm n :=
  denominator (point q (argument z) R B A) (unit q)*unit p
def realBound (p q z R B A : PTm n) : PTm n :=
  RationalArithmetic.add (GaussianEulerVerticalShiftedRadius.shiftedScalar (point q (argument z) R B A) (unit q))
    (fraction one (unit p))

private theorem nonnegative_radius_base (q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    upper scalarZero (fstT (point q (argument z) R B A)) one (unit q) := by
  let c : PTm n := fraction one (num 18)
  let y := fstT (point q (argument z) R B A)
  have h18 : Γ ⊢[PRAAx] le one (num 18) := le_of_eq_add (d := num 17) (by ipra_ring)
  have nonnegative : Γ ⊢[PRAAx] upper scalarZero c zero one := by
    apply RationalRepresentedUpper.from_signed scalarZero c (ZT.ofNat zero) (ZT.ofNat one) one (num 18) zero one
      (le_refl one) h18 (RationalGaussianEmbedding.scalar_zero_represents one) (fraction_represents one (num 18) h18)
    apply zle_of_toZ one
    simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    ipra_simps
    ring
  have native := GaussianEulerVerticalNativeProjection.lower_source z R B A h.andE₁
  have low : Γ ⊢[PRAAx] upper c y one (unit q) :=
    GaussianEulerIntegralPositiveLower.original_gamma_positive_lower q (argument z) R B A
      (.andI native (GaussianEulerVerticalNativeProjection.imaginary_zero z)) h.andE₂
  have joined := upper_triangle _ _ _ _ _ _ _ nonnegative low
  exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) joined

theorem radius_value (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (realBound p q z R B A) (ZT.ofNat (radiusNumerator p q z R B A))
      (radiusDenominator p q z R B A) := by
  let y := point q (argument z) R B A
  have base := GaussianEulerVerticalShiftedRadius.shifted_represents y (unit q) (unit_positive q)
    (nonnegative_radius_base q z R B A h)
  have add := RationalRepresentations.represents_add _ _ _ _ _ _ base (fraction_represents one (unit p) (unit_positive p))
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) add
  ipra_lc [radiusNumerator]

private theorem cutoff_coordinate (t A R : PTm n) : Γ ⊢[PRAAx]
    upper (fstT (cutoffRadius (t+num 4) t A R)) (fstT qzero) one (unit t) := by
  let k := t+num 4
  let C := GaussianGammaCompactQuadratureBoundary.width t A R
  let P := GaussianCompactRiemannName.precision k (GaussianGammaIntegralCutoffs.top t A R)
  let D := GaussianGammaIntegralCutoffs.etaDen t A R*unit P
  have dpos : Γ ⊢[PRAAx] le one D := positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive t A R) (unit_positive P)
  have u := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right t (num 4))
  have allow : Γ ⊢[PRAAx] le (C*num 4*unit t) D :=
    le_trans (LeanProofs.IPRA.mul_le_mul_right (C*num 4) u |> le_congr (by ipra_ring) (by ipra_ring))
      (cutoff_radius_budget k t A R)
  have norm : Γ ⊢[PRAAx] bounded (cutoffRadius k t A R) one (unit t) :=
    bounded_radius_mono _ _ _ _ _ dpos (unit_positive t) (le_congr (.eqRefl _) (by ipra_ring) allow)
      (GaussianDominantPairAlgebra.radius_bounded (C*num 4) D dpos)
  exact upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive t)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive t)).iffMpr norm))

private theorem companion_coordinate (q t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    upper (fstT (qadd (ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data (argument z) R B A))
      (cutoffRadius (t+num 4) t A R))) (fstT (point q (argument z) R B A))
      (two*unit q+unit t) (unit t*unit q) := by
  let y := point q (argument z) R B A
  let x := ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data (argument z) R B A)
  let r := cutoffRadius (t+num 4) t A R
  have realSource : Γ ⊢[PRAAx] source (argument z) R B A :=
    .andI (GaussianEulerVerticalNativeProjection.lower_source z R B A h.andE₁) h.andE₂
  have realDistance := cross_at _ _ _ _ t q (original_Euler_integral_is_Gamma (argument z) R B A realSource)
  have den := positive_product _ _ (unit_positive (Γ := Γ) t) (unit_positive q)
  have reUpper := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ den realDistance)
  have joined := RationalUpperAddition.add_upper (fstT x) (fstT y) (fstT r) (fstT qzero) _ _ _ _ reUpper
    (cutoff_coordinate t A R)
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical y := GaussianNameReciprocal.name_canonical _ _ _ _
  have eqY := (GaussianReciprocalHorner.qadd_commutative y qzero).eqTrans (GaussianRationalSyntheticDivision.qzero_add y hc)
  have original := upper_congr (RationalGaussianRealPart.real_add x r).eqSymm
    ((RationalGaussianRealPart.real_add y qzero).eqSymm.eqTrans (congrFst eqY)) (.eqRefl _) (.eqRefl _) joined
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ den (unit_positive t)) original
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))

private theorem original_slack (p q t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    slack (point p z R B A) (radiusNumerator p q z R B A) (radiusDenominator p q z R B A) (num 3) t := by
  let y := point q (argument z) R B A
  have margin := nonnegative_radius_base q z R B A h
  have rows := GaussianEulerVerticalQuadrature.original_improper_bound t z R B A h.andE₁.andE₂.andE₁
  have comp := GaussianEulerVerticalShiftedRadius.enlarged_norm_after_shift _ _ y (unit q) two (unit t)
    (unit_positive q) (unit_positive t) rows margin (companion_coordinate q t z R B A h)
  have den := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive t)
  have step := cross_at _ _ _ _ p t (cross_symm _ _ _ _ (original_Euler_integral_is_Gamma z R B A h))
  have second := positive_product (Γ := Γ) _ _ (denominator_positive y (unit q) (unit_positive q)) (unit_positive t)
  have total := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den second step comp
  have goalDen := positive_product _ _
    (positive_product (Γ := Γ) _ _ (denominator_positive y (unit q) (unit_positive q)) (unit_positive p)) (unit_positive t)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ den second) goalDen
    (le_congr (by unfold radiusNumerator radiusDenominator unit; ipra_ring) (.eqRefl _) (le_refl _)) total

theorem original_gamma_vertical_bound (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    bounded (point p z R B A) (radiusNumerator p q z R B A) (radiusDenominator p q z R B A) :=
  slack_removal_at _ _ _ (num 3) (positive_product _ _ (denominator_positive _ _ (unit_positive q)) (unit_positive p))
    (original_slack p q _ z R B A h)

theorem original_Gamma_vertical_independent_queries_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      bounded (point (var 0) (var 2) (var 3) (var 4) (var 5))
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
      RationalArithmetic.represents (realBound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (ZT.ofNat (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.andI (original_gamma_vertical_bound _ _ _ _ _ _ Prf.hyp0) (radius_value _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalGammaBound
