import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalNamedReference
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerVerticalGammaBound
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower
import IPRADerivations.Analysis.Names.RationalReciprocalPowerName
import IPRADerivations.Core.CertificateTactics

/-!
# Vertical domination at arbitrary regular named Gamma inputs

Both requested observations are from the original named Gamma frontend.
A single late actual input observation supplies the complex and native
real references in a common numerical disk. All temporary comparison
errors are removed by one finite rational gap. The resulting radius is
the actual real Gamma observation plus exactly the two requested errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedGammaBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source radius numerator denominator threshold)
open GaussianGammaRealValues (axisF)
open GaussianNamedGamma (nameF data)
open GaussianEulerVerticalNamedRadius (commonRadius)
open GaussianGammaHalfPlaneInputContinuity (modulus)
open GaussianEulerVerticalRealRadius (gap denominator_positive)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianPositiveRadiusFiniteSum (boundBy)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalGaussianEmbedding (embed scalarZero)
open RationalValueBounds (upper upper_of_radius radius_symmetric upper_triangle upper_congr upper_mono)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (f : PR 2) (p x A : PTm n) : PTm n := ap2 (nameF f) p (data x A)
def realPoint (f : PR 2) (q x A : PTm n) : PTm n := point (axisF f) q x A
def radiusNumerator (f : PR 2) (p q x A : PTm n) : PTm n :=
  gap (realPoint f q x A) (unit q)*unit p+GaussianEulerVerticalRealRadius.denominator (realPoint f q x A) (unit q)
def radiusDenominator (f : PR 2) (p q x A : PTm n) : PTm n :=
  GaussianEulerVerticalRealRadius.denominator (realPoint f q x A) (unit q)*unit p
def realBound (f : PR 2) (p q x A : PTm n) : PTm n :=
  RationalArithmetic.add (GaussianEulerVerticalShiftedRadius.shiftedScalar (realPoint f q x A) (unit q)) (fraction one (unit p))
def clock (f : PR 2) (s x A : PTm n) : PTm n :=
  threshold A+succ (modulus s (radius f x) (two*A))+succ (modulus s (radius (axisF f) x) (two*A))

private theorem nonnegative_radius_base (f : PR 2) (q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upper scalarZero (fstT (realPoint f q x A)) one (unit q) := by
  let c : PTm n := GaussianNamedGammaPositiveLower.lower
  have h18 : Γ ⊢[PRAAx] le one (num 18) := le_of_eq_add (d := num 17) (by ipra_ring)
  have nonnegative : Γ ⊢[PRAAx] upper scalarZero c zero one := by
    apply RationalRepresentedUpper.from_signed scalarZero c (ZT.ofNat zero) (ZT.ofNat one) one (num 18) zero one
      (le_refl one) h18 (RationalGaussianEmbedding.scalar_zero_represents one) (fraction_represents one (num 18) h18)
    apply zle_of_toZ one
    simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    ipra_simps
    ring
  have low := GaussianNamedGammaPositiveLower.original_gamma_positive_lower (axisF f) q x A
    (.andI (GaussianEulerVerticalProjection.projected_source f x A h) (GaussianEulerVerticalProjection.projected_real_samples f x))
  exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) (upper_triangle _ _ _ _ _ _ _ nonnegative low)

theorem radius_value (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (realBound f p q x A) (ZT.ofNat (radiusNumerator f p q x A)) (radiusDenominator f p q x A) := by
  have base := GaussianEulerVerticalShiftedRadius.shifted_represents (realPoint f q x A) (unit q) (unit_positive q)
    (nonnegative_radius_base f q x A h)
  have add := RationalRepresentations.represents_add _ _ _ _ _ _ base (fraction_represents one (unit p) (unit_positive p))
  apply scalar_congr (.eqRefl _) _ (.eqRefl _) add
  ipra_lc [radiusNumerator]

private theorem late_complex (f : PR 2) (s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedGammaLateInput.input f s (clock f s x A) x A :=
  .andI h (.andI (le_trans (le_add_right _ _) (le_add_right _ _)) (le_trans (le_add_left _ _) (le_add_right _ _)))

private theorem encoded_source (f : PR 2) (s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianEulerIntegralGammaIdentification.source (numerator f (clock f s x A) x) (commonRadius f x)
      (denominator f (clock f s x A) x) (two*A) :=
  GaussianEulerVerticalNamedRadius.source_enlarge _ _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source f s (clock f s x A) x A (late_complex f s x A h))
    (GaussianEulerVerticalNamedRadius.common_radius_bounds f x).andE₁

private theorem encoded_radius_bound (s z R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A) : Γ ⊢[PRAAx]
    boundBy (GaussianEulerVerticalGammaBound.point s z R B A) (embed (GaussianEulerVerticalGammaBound.realBound s s z R B A)) := by
  let r := GaussianEulerVerticalGammaBound.realBound s s z R B A
  let D := GaussianEulerVerticalGammaBound.radiusDenominator s s z R B A
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _
    (GaussianEulerVerticalRealRadius.denominator_positive _ _ (unit_positive s)) (unit_positive s)
  have rep := GaussianEulerVerticalGammaBound.radius_value s s z R B A h
  have first : Γ ⊢[PRAAx] fstT (embed r) ≐ r := (fst_pair _ _).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _))
  exact GaussianPositiveRadiusFiniteSum.from_representation _ _ _ _ hd
    (GaussianPositiveRealArithmetic.positive_embed r (GaussianRationalL1.nonnegative_of_representation _ _ _ hd rep))
    (scalar_congr first.eqSymm (.eqRefl _) (.eqRefl _) rep)
    (GaussianEulerVerticalGammaBound.original_gamma_vertical_bound s s z R B A h)

private theorem companion_coordinate (f : PR 2) (q t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upper (fstT (embed (GaussianEulerVerticalGammaBound.realBound t t
      (numerator f (clock f t x A) x) (commonRadius f x) (denominator f (clock f t x A) x) (two*A))))
      (fstT (realPoint f q x A)) (num 4*unit q+unit t) (unit t*unit q) := by
  let r := clock f t x A
  let E := ap2 GaussianGammaReciprocalInverse.gammaF t (GaussianEulerVerticalNamedReference.realEncodedData f r x A (commonRadius f x))
  let V := GaussianEulerVerticalGammaBound.realBound t t (numerator f r x) (commonRadius f x) (denominator f r x) (two*A)
  have projected := GaussianEulerVerticalNamedReference.projected_independent_rate f t r x A (commonRadius f x) h
    (late_complex f t x A h).andE₂.andE₁ (le_add_left _ _)
    (GaussianEulerVerticalNamedRadius.common_radius_bounds f x).andE₁ (GaussianEulerVerticalNamedRadius.common_radius_bounds f x).andE₂
  have near := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ q t projected
  have d := denominator_positive (Γ := Γ) (unit t) q t (unit_positive t)
  have coord := upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ (scalar_coordinate_distance _ _ _ _ d near))
  have inner := RationalReciprocalPowerName.fraction_add_upper (Γ := Γ) (fstT E) one (unit t) (unit_positive t)
  have outer := RationalReciprocalPowerName.fraction_add_upper (Γ := Γ) (GaussianEulerVerticalShiftedRadius.shiftedScalar E (unit t)) one (unit t) (unit_positive t)
  have twice := upper_triangle _ _ _ _ _ _ _ outer inner
  have total := upper_triangle _ _ _ _ _ _ _ twice coord
  have first : Γ ⊢[PRAAx] fstT (embed V) ≐ V := (fst_pair _ _).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) d)
    (upper_congr first.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) total)
    (le_congr (by dsimp only [rateNumerator,rateDenominator]; ipra_ring) (.eqRefl _) (le_refl _))

private theorem original_slack (f : PR 2) (p q t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    slack (point f p x A) (radiusNumerator f p q x A) (radiusDenominator f p q x A) (num 6) t := by
  let y := realPoint f q x A
  let r := clock f t x A
  have margin := nonnegative_radius_base f q x A h
  have rows := encoded_radius_bound t _ _ _ _ (encoded_source f t x A h)
  have comp := GaussianEulerVerticalShiftedRadius.enlarged_norm_after_shift _ _ y (unit q) (num 4) (unit t)
    (unit_positive q) (unit_positive t) rows margin (companion_coordinate f q t x A h)
  have step := GaussianEulerVerticalNamedRadius.original_observations f p t t r x A (commonRadius f x)
    (late_complex f t x A h) (GaussianEulerVerticalNamedRadius.common_radius_bounds f x).andE₁
  have den := denominator_positive (Γ := Γ) (unit t) p t (unit_positive t)
  have second := positive_product (Γ := Γ) _ _ (GaussianEulerVerticalRealRadius.denominator_positive y (unit q) (unit_positive q)) (unit_positive t)
  have total := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den second step comp
  have goalDen := positive_product _ _
    (positive_product (Γ := Γ) _ _ (GaussianEulerVerticalRealRadius.denominator_positive y (unit q) (unit_positive q)) (unit_positive p)) (unit_positive t)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ den second) goalDen
    (le_congr (by unfold radiusNumerator radiusDenominator rateNumerator rateDenominator unit; ipra_ring) (.eqRefl _) (le_refl _)) total

theorem original_named_gamma_vertical_bound (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    bounded (point f p x A) (radiusNumerator f p q x A) (radiusDenominator f p q x A) :=
  slack_removal_at _ _ _ (num 6) (positive_product _ _
    (GaussianEulerVerticalRealRadius.denominator_positive _ _ (unit_positive q)) (unit_positive p)) (original_slack f p q _ x A h)

theorem original_named_Gamma_vertical_independent_queries_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 2) (var 3) ⟶
      bounded (point f (var 0) (var 2) (var 3)) (radiusNumerator f (var 0) (var 1) (var 2) (var 3))
        (radiusDenominator f (var 0) (var 1) (var 2) (var 3)) ⋏
      RationalArithmetic.represents (realBound f (var 0) (var 1) (var 2) (var 3))
        (ZT.ofNat (radiusNumerator f (var 0) (var 1) (var 2) (var 3))) (radiusDenominator f (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.andI (original_named_gamma_vertical_bound f _ _ _ _ Prf.hyp0) (radius_value f _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedGammaBound
