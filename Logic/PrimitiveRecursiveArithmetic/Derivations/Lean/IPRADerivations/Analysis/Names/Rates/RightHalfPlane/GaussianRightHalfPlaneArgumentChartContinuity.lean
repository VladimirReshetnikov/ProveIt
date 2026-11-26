import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentForwardLipschitz
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialUnitEndpoint
import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneArgumentExponential
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Continuity of the two original right-half-plane argument charts

Use the forward quadrature bound at the literal clock of the small
chart. In the reciprocal chart the variable part is subtracted from
the original quarter turn. The charts meet at unit ratio.
-/

set_option autoImplicit false
set_option maxHeartbeats 830000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentChartContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNamedDifference (difference_distance sample_error name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRightHalfPlaneArgument (smallF smallData largeF largeData half_bounded small_regular)
open RationalCubeMidpoint (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "Q" => GaussianArctangentPartialQuadrature.nameF
local notation "P" => GaussianArctangentPartialQuadrature.data
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data

theorem small_distance (p A B a b H K : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (ha : Γ ⊢[PRAAx] le one a)
    (hB : Γ ⊢[PRAAx] le B A) (hb : Γ ⊢[PRAAx] le b a) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (fraction B A) (fraction b a) H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 smallF p (smallData A B)) (ap2 smallF p (smallData a b))
      (two*H*unit p+two*K) (K*unit p) := by
  let t := GaussianBoundedConstantProductName.clock p one
  let T := unit t
  let U := unit p
  let c : PTm n := GaussianRightHalfPlaneArgument.half
  let w := ap2 Q t (P B A)
  let v := ap2 Q t (P b a)
  have hT := unit_positive (Γ := Γ) t
  have hU := unit_positive (Γ := Γ) p
  have hOld := positive_product _ _ (positive_product _ _ hT hT) hK
  have hNew := positive_product _ _ hK hU
  have base := GaussianArctangentForwardLipschitz.forward_distance t t B A b a H K hA ha hB hb hK h
  have scale := GaussianApproximateInverseDistance.multiply_distance c w v one _ _ hOld half_bounded base
  have literal := distance_congr
    (GaussianBoundedConstantProductName.sample_at Q p one c (P B A)).eqSymm
    (GaussianBoundedConstantProductName.sample_at Q p one c (P b a)).eqSymm (one_mul _) (.eqRefl _) scale
  have later : Γ ⊢[PRAAx] le p t := le_add_right p _
  have grow := GaussianExponentialReference.unit_monotone later
  exact distance_radius_mono _ _ ((T+T)*K+two*H*(T*T)) ((T*T)*K)
    (two*H*U+two*K) (K*U) hOld hNew (by ipra_le 2*𝔞(K)^2*𝔞(T)*sl grow) literal

theorem large_distance (p A B a b H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hA : Γ ⊢[PRAAx] le A B) (ha : Γ ⊢[PRAAx] le a b) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (fraction A B) (fraction a b) H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 largeF p (largeData A B)) (ap2 largeF p (largeData a b))
      (two*H*unit p+num 14*K) (K*unit p) := by
  let u := unit p
  let d := K*u
  let x := smallData B A
  let y := smallData b a
  let v := ap2 quarterF p zero
  let w := ap2 smallF p x
  let z := ap2 smallF p y
  let l := ap2 largeF p (largeData A B)
  let r := ap2 largeF p (largeData a b)
  have hu := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hK hu
  have first : Γ ⊢[PRAAx] distanceBounded l (qsub v w) (num 6) u :=
    sample_error quarterF smallF zero x p (quarter_regular zero) (small_regular B A hB hA)
  have last : Γ ⊢[PRAAx] distanceBounded r (qsub v z) (num 6) u :=
    sample_error quarterF smallF zero y p (quarter_regular zero) (small_regular b a hb ha)
  have narrow (a b : PTm n) (h : Γ ⊢[PRAAx] distanceBounded a b (num 6) u) :
      Γ ⊢[PRAAx] distanceBounded a b (num 6*K) d :=
    distance_radius_mono _ _ _ _ _ _ hu hd (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) h
  have middle := difference_distance v v w z zero (two*H*u+two*K) d hd
    (distance_refl_zero v d hd) (small_distance p B A b a H K hB hb hA ha hK h)
  have firstTwo := distance_triangle_same l (qsub v w) (qsub v z) _ _ d hd (narrow _ _ first) middle
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same l (qsub v z) r _ _ d hd firstTwo
      (narrow _ _ (distance_symmetric _ _ _ _ hu last)))

theorem chart_boundary : Γ ⊢[PRAAx] crossEquivalent largeF smallF
    (largeData (one : PTm n) one) (smallData one one) := by
  let x := smallData (one : PTm n) one
  have hx := small_regular (Γ := Γ) one one (le_refl one) (le_refl one)
  have hq := quarter_regular (Γ := Γ) (zero : PTm n)
  have double := cross_trans (Γ := Γ) (addF smallF smallF) Q quarterF (addData x x) (P one one) zero
    (GaussianRightHalfPlaneArgumentExponential.small_double _ _ (le_refl one) (le_refl one))
    (GaussianArctangentPartialUnitEndpoint.unit_endpoint_cross zero)
  have moved := GaussianNamedDifferenceQuotientProperness.difference_proper quarterF
    (addF smallF smallF) smallF smallF zero (addData x x) x x hq (add_fast _ _ _ _ hx hx) hx hx
    (cross_symm _ _ _ _ double) (cross_refl _ _ hx)
  exact cross_trans largeF (F (addF smallF smallF) smallF) smallF (largeData one one) (X (addData x x) x) x
    moved (GaussianNamedStrictOrderDifference.sum_sub_right smallF smallF x x hx hx)

theorem mixed_distance (p A B a b H K : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hb : Γ ⊢[PRAAx] le one b)
    (hB : Γ ⊢[PRAAx] le B A) (ha : Γ ⊢[PRAAx] le a b) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (fraction B A) (fraction one one) H K)
    (g : Γ ⊢[PRAAx] RationalValueBounds.radius (fraction one one) (fraction a b) H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 smallF p (smallData A B)) (ap2 largeF p (largeData a b))
      (num 4*H*unit p+num 18*K) (K*unit p) := by
  let u := unit p
  let d := K*u
  let w := ap2 smallF p (smallData A B)
  let x := ap2 smallF p (smallData one one)
  let y := ap2 largeF p (largeData one one)
  let z := ap2 largeF p (largeData a b)
  have hu := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hK hu
  have first := small_distance p A B one one H K hA (le_refl one) hB (le_refl one) hK h
  have last := large_distance p one one a b H K (le_refl one) hb (le_refl one) ha hK g
  have mid := GaussianNameEquivalence.cross_at (Γ := Γ) smallF largeF (smallData one one) (largeData one one) p p
    (cross_symm _ _ _ _ chart_boundary)
  have paid := distance_radius_mono x y (u+u) (u*u) (two*K) d
    (positive_product _ _ hu hu) hd (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) mid
  have left := distance_triangle_same w x y _ _ d hd first paid
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same w y z _ _ d hd left last)

theorem actual_right_half_plane_argument_charts_meet_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent largeF smallF (largeData one one) (smallData one one) :=
  chart_boundary

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentChartContinuity
