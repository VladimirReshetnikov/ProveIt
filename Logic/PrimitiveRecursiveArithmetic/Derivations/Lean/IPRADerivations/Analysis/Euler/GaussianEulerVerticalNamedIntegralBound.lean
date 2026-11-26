import IPRADerivations.Analysis.Gamma.Names.GaussianEulerVerticalNamedGammaBound
import IPRADerivations.Core.CertificateTactics

/-!
# Vertical domination for the original named improper Euler integral

Exact original named Euler--Gamma equivalence transfers the vertical
bound to both literal named quadrature programs. The independent
requested observations keep their own errors, and a finite rational gap
removes the four temporary errors introduced by the two comparisons.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedIntegralBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source)
open GaussianGammaRealValues (axisF)
open GaussianNamedGamma (data)
open GaussianEulerVerticalRealRadius (gap)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianRationalMetric (bounded)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianPositiveRadiusFiniteSum (boundBy)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalGaussianEmbedding (embed scalarZero)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_congr upper_mono)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (f : PR 2) (p x A : PTm n) : PTm n := ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A)
def realPoint (f : PR 2) (q x A : PTm n) : PTm n := point (axisF f) q x A
def radiusNumerator (f : PR 2) (p q x A : PTm n) : PTm n :=
  gap (realPoint f q x A) (unit q)*unit p+GaussianEulerVerticalRealRadius.denominator (realPoint f q x A) (unit q)
def radiusDenominator (f : PR 2) (p q x A : PTm n) : PTm n :=
  GaussianEulerVerticalRealRadius.denominator (realPoint f q x A) (unit q)*unit p
def realBound (f : PR 2) (p q x A : PTm n) : PTm n :=
  RationalArithmetic.add (GaussianEulerVerticalShiftedRadius.shiftedScalar (realPoint f q x A) (unit q)) (fraction one (unit p))

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
  have low := GaussianNamedGammaPositiveLower.original_improper_positive_lower (axisF f) q x A
    (.andI (GaussianEulerVerticalProjection.projected_source f x A h) (GaussianEulerVerticalProjection.projected_real_samples f x))
  exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) (upper_triangle _ _ _ _ _ _ _ nonnegative low)

theorem radius_value (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (realBound f p q x A) (ZT.ofNat (radiusNumerator f p q x A)) (radiusDenominator f p q x A) := by
  have base := GaussianEulerVerticalShiftedRadius.shifted_represents (realPoint f q x A) (unit q) (unit_positive q)
    (nonnegative_radius_base f q x A h)
  have add := RationalRepresentations.represents_add _ _ _ _ _ _ base (fraction_represents one (unit p) (unit_positive p))
  apply scalar_congr (.eqRefl _) _ (.eqRefl _) add
  ipra_lc [radiusNumerator]

private theorem Gamma_radius_bound (f : PR 2) (t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    boundBy (GaussianEulerVerticalNamedGammaBound.point f t x A) (embed (GaussianEulerVerticalNamedGammaBound.realBound f t t x A)) := by
  let r := GaussianEulerVerticalNamedGammaBound.realBound f t t x A
  let D := GaussianEulerVerticalNamedGammaBound.radiusDenominator f t t x A
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _
    (GaussianEulerVerticalRealRadius.denominator_positive _ _ (unit_positive t)) (unit_positive t)
  have rep := GaussianEulerVerticalNamedGammaBound.radius_value f t t x A h
  have first : Γ ⊢[PRAAx] fstT (embed r) ≐ r := (fst_pair _ _).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _))
  exact GaussianPositiveRadiusFiniteSum.from_representation _ _ _ _ hd
    (GaussianPositiveRealArithmetic.positive_embed r (GaussianRationalL1.nonnegative_of_representation _ _ _ hd rep))
    (scalar_congr first.eqSymm (.eqRefl _) (.eqRefl _) rep)
    (GaussianEulerVerticalNamedGammaBound.original_named_gamma_vertical_bound f t t x A h)

private theorem companion_coordinate (f : PR 2) (q t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upper (fstT (embed (GaussianEulerVerticalNamedGammaBound.realBound f t t x A)))
      (fstT (realPoint f q x A)) (num 3*unit q+unit t) (unit t*unit q) := by
  let E := GaussianEulerVerticalNamedGammaBound.realPoint f t x A
  let V := GaussianEulerVerticalNamedGammaBound.realBound f t t x A
  have projected := GaussianEulerVerticalProjection.projected_source f x A h
  have equivalence := GaussianNamedEulerQuadrature.original_named_Euler_integral_is_Gamma (axisF f) x A projected
  have near := cross_at _ _ _ _ t q (cross_symm _ _ _ _ equivalence)
  have d := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive q)
  have coord := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ d near)
  have inner := RationalReciprocalPowerName.fraction_add_upper (Γ := Γ) (fstT E) one (unit t) (unit_positive t)
  have outer := RationalReciprocalPowerName.fraction_add_upper (Γ := Γ) (GaussianEulerVerticalShiftedRadius.shiftedScalar E (unit t)) one (unit t) (unit_positive t)
  have twice := upper_triangle _ _ _ _ _ _ _ outer inner
  have total := upper_triangle _ _ _ _ _ _ _ twice coord
  have first : Γ ⊢[PRAAx] fstT (embed V) ≐ V := (fst_pair _ _).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) d)
    (upper_congr first.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) total)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))

private theorem original_slack (f : PR 2) (p q t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    slack (point f p x A) (radiusNumerator f p q x A) (radiusDenominator f p q x A) (num 4) t := by
  let y := realPoint f q x A
  have margin := nonnegative_radius_base f q x A h
  have rows := Gamma_radius_bound f t x A h
  have comp := GaussianEulerVerticalShiftedRadius.enlarged_norm_after_shift _ _ y (unit q) (num 3) (unit t)
    (unit_positive q) (unit_positive t) rows margin (companion_coordinate f q t x A h)
  have step := cross_at _ _ _ _ p t (GaussianNamedEulerQuadrature.original_named_Euler_integral_is_Gamma f x A h)
  have den := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
  have second := positive_product (Γ := Γ) _ _ (GaussianEulerVerticalRealRadius.denominator_positive y (unit q) (unit_positive q)) (unit_positive t)
  have total := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den second step comp
  have goalDen := positive_product _ _
    (positive_product (Γ := Γ) _ _ (GaussianEulerVerticalRealRadius.denominator_positive y (unit q) (unit_positive q)) (unit_positive p)) (unit_positive t)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ den second) goalDen
    (le_congr (by unfold radiusNumerator radiusDenominator unit; ipra_ring) (.eqRefl _) (le_refl _)) total

theorem original_named_Euler_vertical_bound (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    bounded (point f p x A) (radiusNumerator f p q x A) (radiusDenominator f p q x A) :=
  slack_removal_at _ _ _ (num 4) (positive_product _ _
    (GaussianEulerVerticalRealRadius.denominator_positive _ _ (unit_positive q)) (unit_positive p)) (original_slack f p q _ x A h)

theorem original_named_Euler_vertical_independent_queries_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 2) (var 3) ⟶
      bounded (point f (var 0) (var 2) (var 3)) (radiusNumerator f (var 0) (var 1) (var 2) (var 3))
        (radiusDenominator f (var 0) (var 1) (var 2) (var 3)) ⋏
      RationalArithmetic.represents (realBound f (var 0) (var 1) (var 2) (var 3))
        (ZT.ofNat (radiusNumerator f (var 0) (var 1) (var 2) (var 3))) (radiusDenominator f (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.andI (original_named_Euler_vertical_bound f _ _ _ _ Prf.hyp0) (radius_value f _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedIntegralBound
