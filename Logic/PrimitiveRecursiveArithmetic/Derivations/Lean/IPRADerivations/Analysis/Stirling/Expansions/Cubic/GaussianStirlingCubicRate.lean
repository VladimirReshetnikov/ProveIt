import IPRADerivations.Analysis.Stirling.Expansions.Cubic.GaussianStirlingCubicBound
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeStrongLogConvexity
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingExpansionFirstOrder
import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingFactorialRobbinsExponential

/-!
# The cubic rate on the original Stirling remainder

Cancel the constant cubic term at the level of ordered names. The resulting
bracket gives the cubic observation rate with the same independent clocks
as the multiplicative Stirling error program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingCubicRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedGammaHalfShift (constant_sum)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance constant_order)
open GaussianRationalHorner (qadd qzero canonical ofGaussian_canonical positive_product)
open GaussianRationalMetric (qsub qsub_canonical distanceBounded bounded)
open GaussianReciprocalHorner (qsub_add_cancel qadd_zero_right)
open GaussianStirlingCubicBound (correctedF correctedData original_cubic_bound)
open GaussianStirlingCubicCell (cube cubicValue cube_positive cubic_den_positive)
open GaussianStirlingGlobalBounds (remainderF remainderData remainder_regular)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (upperValue upper_den_positive)
open GaussianStirlingTailComparison (point_add_upper_same)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def lowerValue (a b : PTm n) : PTm n := qsub (upperValue a b) (cubicValue a b)

set_option maxHeartbeats 600000 in
theorem lower_strict (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] strictOrder constantF remainderF (lowerValue a b) (remainderData a b x) := by
  let U := upperValue a b
  let V := cubicValue a b
  let W := lowerValue a b
  let X := remainderData a b x
  have h := original_cubic_bound a b x hs
  have hU : Γ ⊢[PRAAx] canonical U := ofGaussian_canonical _ _ (upper_den_positive a hs.andE₁)
  have hV := constant_regular (Γ := Γ) V
  have hW := constant_regular (Γ := Γ) W
  have hx := remainder_regular a b x hs
  have left := constant_sum V W U (GaussianRationalLinearProduct.add_sub_right V U hU)
  have right := GaussianNameRingLaws.add_commutative remainderF constantF X V hx hV
  have all : Γ ⊢[PRAAx] realOrder (addF constantF constantF) (addF constantF remainderF) (addData V W) (addData V X) :=
    GaussianNamedRealOrderTransport.transport (addF constantF constantF) constantF correctedF (addF constantF remainderF)
      (addData V W) U (correctedData a b x) (addData V X) left right h.andE₁
  refine .andI (GaussianGammaStrongLogConvexityAlgebra.cancel_common constantF constantF remainderF V W X hV hW hx all) (.impI ?_)
  have inv := add_order constantF constantF remainderF constantF V V X W (order_refl _ _ hV.wk) Prf.hyp0
  exact h.andE₂.wk.impE (GaussianNamedRealOrderTransport.transport correctedF (addF constantF remainderF)
    (addF constantF constantF) constantF (correctedData a b x) (addData V X) (addData V W) U right.wk left.wk inv)

theorem actual_positive_rational_signed_Stirling_bracket_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶
      strictOrder constantF remainderF (lowerValue (var 0) (var 1)) (remainderData (var 0) (var 1) (var 2)) ⋏
      strictOrder remainderF constantF (remainderData (var 0) (var 1) (var 2)) (upperValue (var 0) (var 1))) := by
  refine closeUniv 3 (.impI (.andI (lower_strict _ _ _ Prf.hyp0) ?_))
  exact GaussianStirlingFactorialRobbinsExponential.upper_log_strict _ _ _ Prf.hyp0
    (GaussianStirlingGammaFractionalIncrement.original_first_order _ _ _ Prf.hyp0).andE₂

private theorem tail_upper (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] upper (fstT (cubicValue a b)) (fstT qzero) (cube b) (cube a) := by
  let P := cube b
  let Q := cube a
  let B := num 360*Q
  let C := cubicValue a b
  have hD := cube_positive a ha
  have hB := cubic_den_positive a ha
  have raw := GaussianDominantPairAlgebra.radius_bounded P B hB
  have bound := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point P B hB).eqSymm (.eqRefl _) (.eqRefl _) raw
  have cmp : Γ ⊢[PRAAx] le (P*Q) (P*(num 360*Q)) := by ipra_le 359*𝔞 P*𝔞 Q
  have near : Γ ⊢[PRAAx] bounded C P Q :=
    bounded_radius_mono _ _ _ _ _ hB hD cmp bound
  have eq := GaussianRationalReconstruction.qsub_zero_right C (ofGaussian_canonical _ _ hB)
  exact upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD
    (GaussianRationalReciprocal.bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) near))

private theorem lower_at (p q a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (upperValue a b)) (fstT (ap2 remainderF p (remainderData a b x)))
      (rateNumerator (cube b) (cube a) p q) (rateDenominator (cube a) p q) := by
  let X := remainderData a b x
  let Z := ap2 remainderF p X
  let L := lowerValue a b
  let C := cubicValue a b
  let u := unit p
  let v := unit q
  let B := cube a
  let N := rateDenominator B p q
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hB := cube_positive a hs.andE₁
  have hN := positive_product _ _ (positive_product _ _ hB hu) hv
  have low := upper_congr (congrFst (constant_at q L)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (real_order_at constantF remainderF L X q p (lower_strict a b x hs).andE₁)
  have lifted : Γ ⊢[PRAAx] upper (fstT L) (fstT Z) (B*(u+v)) N :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hv hu) low
      (le_of_eq_add (d := zero) (by dsimp only [N,rateDenominator]; ipra_ring))
  have tail : Γ ⊢[PRAAx] upper (fstT C) (fstT qzero) (cube b*u*v) N :=
    upper_mono _ _ _ _ _ _ hB (tail_upper a b hs.andE₁)
      (le_of_eq_add (d := zero) (by dsimp only [N,rateDenominator]; ipra_ring))
  have full := point_add_upper_same L Z C qzero (B*(u+v)) (cube b*u*v) N hN lifted tail
  have hU : Γ ⊢[PRAAx] canonical (upperValue a b) := ofGaussian_canonical _ _ (upper_den_positive a hs.andE₁)
  have hZ := (GaussianSignedNameExponentialOrder.real_sample_at remainderF X p
    (GaussianStirlingMultiplicativeBounds.remainder_real a b x hs)).andE₁
  have eq := (GaussianReciprocalHorner.qadd_commutative L C).eqTrans
    (GaussianRationalLinearProduct.add_sub_right C (upperValue a b) hU)
  exact upper_congr (congrFst eq) (congrFst (qadd_zero_right Z hZ))
    (by dsimp only [rateNumerator]; ipra_ring) (.eqRefl _) full

theorem cubic_rate_at (p q a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 remainderF p (remainderData a b x)) (ap2 constantF q (upperValue a b))
      (rateNumerator (cube b) (cube a) p q) (rateDenominator (cube a) p q) := by
  let X := remainderData a b x
  let Z := ap2 remainderF p X
  let Q := upperValue a b
  let B := cube a
  let M := rateNumerator (cube b) B p q
  let N := rateDenominator B p q
  have ws := GaussianStirlingGammaFractionalIncrement.original_first_order a b x hs
  have bound := (GaussianStirlingFactorialRobbinsExponential.upper_log_strict a b x hs ws.andE₂).andE₁
  have upperBound := upper_congr (.eqRefl _) (congrFst (constant_at q Q)) (.eqRefl _) (.eqRefl _)
    (real_order_at remainderF constantF X Q p q bound)
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hN := GaussianNamedInverseRate.denominator_positive B p q (cube_positive _ hs.andE₁)
  have hi : Γ ⊢[PRAAx] upper (fstT Z) (fstT Q) M N :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hu hv) upperBound
      (by dsimp only [M,N,rateNumerator,rateDenominator]; ipra_le 𝔞 (cube b)*(𝔞 (unit p)*𝔞 (unit q))^2)
  have range := radius_of_upper _ _ _ _ hi (lower_at p q a b x hs)
  have zr := GaussianSignedNameExponentialOrder.real_sample_at remainderF X p
    (GaussianStirlingMultiplicativeBounds.remainder_real a b x hs)
  have qr := GaussianStirlingNames.fraction_axis b (num 12*a) (upper_den_positive a hs.andE₁)
  have qc : Γ ⊢[PRAAx] canonical Q := ofGaussian_canonical _ _ (upper_den_positive a hs.andE₁)
  exact GaussianRationalDistanceOrder.distance_congr
    (RationalGaussianEmbedding.canonical_axis_roundtrip Z zr.andE₁ zr.andE₂)
    ((RationalGaussianEmbedding.canonical_axis_roundtrip Q qc qr).eqTrans (constant_at q Q).eqSymm)
    (.eqRefl _) (.eqRefl _) (RationalGaussianNameEmbedding.distance_from_radius _ _ M N hN range)

end LeanProofs.IPRA.Analysis.GaussianStirlingCubicRate
