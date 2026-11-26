import IPRADerivations.Analysis.Trigonometry.SineProducts.SampleProducts.GaussianSineProductSynchronizedRow

/-!
# Slack in the synchronized sine head-row estimate

The divided root arguments in the first K rows lie in the half disk.
Their squared sinc values therefore stay within one half of one, giving
a reciprocal bound of two. This leaves room in the paper's head-row
budget for the independent finite synchronization error.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT4SharpRow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianArctangentDivisionAngles (modulus)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerReflectionHead (squareFactor)
open GaussianInverseSquareProductComparison (rowErrorNumerator rowErrorDenominator)
open GaussianNamedDifference (difference_distance)
open GaussianNamedSincQuadraticBounds (observationBound quadratic_bound square_quadratic_bound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalLowerBounds (lower name_lower)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (qone reciprocal reciprocal_identity bounded_product bound_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianSincRatioProductRow (base_square_bound)
open GaussianSineProductRelativeArgument (relative)
open GaussianSineProductScaledArguments (nameF)
open GaussianSineProductSynchronizedRow (angleData rootData sincValue sincFactor actualFactor transport budget
  argument_input root_input modulus_eq)
open GaussianSineProductT4Budget (halfIndex multiple squareDenominator denominator_positive argument_disk)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem half_root_disk (R K k : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hk : Γ ⊢[PRAAx] le k K) : Γ ⊢[PRAAx] le (two*(num 4*k)) (modulus (halfIndex R K)) := by
  have v : Γ ⊢[PRAAx] le k ((K*K)*(R*R)) :=
    le_trans hk (le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_mul_mono (le_refl K) hK) (positive_product _ _ hR hR)))
  have grow : Γ ⊢[PRAAx] le (num 8*((K*K)*(R*R))) (multiple R K) := le_succ_self _
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (num 8)) v))
    (le_congr (.eqRefl _) (modulus_eq R K).eqSymm grow)

private theorem square_root_lower (f : PR 2) (r x A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le (two*A) B)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] lower (GaussianNamedSincRatio.square f r x p) one two := by
  have a : Γ ⊢[PRAAx] le A (two*A) := le_congr (.eqRefl _) (by ipra_ring) (le_add_right A A)
  have h3 : Γ ⊢[PRAAx] le (num 3*(A*A)) (B*B) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (num 3*(A*A)) (A*A)))
      (le_mul_mono hAB hAB)
  have den := positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB)
  apply GaussianBoundedInverseApartness.lower_near_one
  exact distance_radius_mono _ _ _ _ _ _ den (le_succ_self one)
    (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right two h3))
    (square_quadratic_bound f r x A B p hB (le_trans a hAB) h)

private theorem ratio_sharp (f g : PR 2) (r x s y A C B p q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (ha : Γ ⊢[PRAAx] le A B) (hc : Γ ⊢[PRAAx] le (two*C) B)
    (hu : Γ ⊢[PRAAx] observationBound f x A B) (hv : Γ ⊢[PRAAx] observationBound g y C B) :
    Γ ⊢[PRAAx] distanceBounded (GaussianNamedSincRatio.ratio f g r x s y p q) qone (num 3*(A*A+C*C)) (B*B) := by
  let u := GaussianNamedSincRatio.square f r x p
  let v := GaussianNamedSincRatio.square g s y q
  let D := two*(B*B)
  have hD := positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB)
  have hC : Γ ⊢[PRAAx] le C B := le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right C C)) hc
  have before := distance_symmetric _ _ _ _ hD (square_quadratic_bound g s y C B q hB hC hv)
  have both := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hD
    (square_quadratic_bound f r x A B p hB ha hu) before
  have low := square_root_lower g s y C B q hB hc hv
  have inv := GaussianRationalLowerBounds.inverse_bound v one two (le_refl one) (le_succ_self one) low
  have exactUnit : Γ ⊢[PRAAx] qmul (reciprocal v) v ≐ qone :=
    (qmul_commutative _ _).eqTrans (reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ _
      (le_succ_self one) (name_lower v one two (le_refl one) (le_succ_self one) low)))
  have raw := distance_congr (.eqRefl _) exactUnit (.eqRefl _) (.eqRefl _)
    (multiply_distance (reciprocal v) u v two _ D hD inv both)
  exact distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ hB hB)
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem corrected_sharp_row (z R B K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i K) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (sincFactor z R B K i x p) (squareFactor i z B)
      (rowErrorNumerator (num 48*(R*R)) (R*R) i) (rowErrorDenominator (squareDenominator R K) i) := by
  let m := modulus (halfIndex R K)
  let k := succ i
  let u := angleData z R B K x
  let v := rootData R K i x
  let a := relative z B k
  let b := GaussianNamedSincRatio.ratio nameF nameF one u one v p p
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hM := positive_product _ _ hm hm
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hk2 := positive_product _ _ hk hk
  have hu := argument_input z R B K x hR hK hB hz
  have hv := root_input R K i x hR hK hi
  have size : Γ ⊢[PRAAx] le (num 4*R) m := le_congr (.eqRefl _) (modulus_eq R K).eqSymm (argument_disk R K hR hK)
  have near := ratio_sharp nameF nameF one u one v (num 4*R) (num 4*k) m p p hm size
    (half_root_disk R K k hR hK hi) hu.andE₂ hv.andE₂
  have diff := bounded_product _ _ _ _ _ _ hk2 hM (base_square_bound i z R B hB hz) near
  have d := distance_congr (.eqRefl _) (qmul_one_right (qmul a a) (qmul_canonical _ _)) (.eqRefl _) (.eqRefl _)
    (bound_congr (GaussianRationalRoundedPower.multiplication_difference (qmul a a) b qone).eqSymm
      (.eqRefl _) (.eqRefl _) diff)
  have hd := positive_product _ _ hk2 hM
  have h := difference_distance qone qone _ _ zero _ _ hd (distance_refl_zero qone _ hd) d
  have hmEq : Γ ⊢[PRAAx] m*m ≐ squareDenominator R K := congrMul (modulus_eq R K) (modulus_eq R K)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold rowErrorNumerator; dsimp only [k]; ipra_ring)
    ((congrMul (.eqRefl _) hmEq).eqTrans (by unfold rowErrorDenominator; dsimp only [k]; ipra_ring)) h

theorem prefactor_bound (z R B K x p : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (sincValue p (angleData z R B K x)) qone (num 8*(R*R)) (squareDenominator R K) := by
  let m := modulus (halfIndex R K)
  let a := angleData z R B K x
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hd := positive_product _ _ (le_succ_self one) (positive_product _ _ hm hm)
  have cap : Γ ⊢[PRAAx] le (num 4*R) m := le_congr (.eqRefl _) (modulus_eq R K).eqSymm (argument_disk R K hR hK)
  have step := quadratic_bound nameF one a (num 4*R) m p hm cap (argument_input z R B K x hR hK hB hz).andE₂
  have e : Γ ⊢[PRAAx] two*(m*m) ≐ two*squareDenominator R K :=
    congrMul (.eqRefl _) (congrMul (modulus_eq R K) (modulus_eq R K))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (le_succ_self one) (denominator_positive R K))
    (denominator_positive R K) (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) e step)

theorem actual_head_row (z R B K i x p : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] lt i K)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hpay : Γ ⊢[PRAAx] le (budget z R B K i x*rowErrorDenominator (squareDenominator R K) i) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (actualFactor z R B K i x p) (squareFactor i z B)
      (rowErrorNumerator (num 96*(R*R)) (R*R) i) (rowErrorDenominator (squareDenominator R K) i) := by
  let D := rowErrorDenominator (squareDenominator R K) i
  let E := rowErrorNumerator (num 48*(R*R)) (R*R) i
  let T := rowErrorNumerator (num 96*(R*R)) (R*R) i
  let H := budget z R B K i x
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (denominator_positive R K)
    (positive_product _ _ (zero_lt_succ _) (zero_lt_succ _))
  have hp := unit_positive (Γ := Γ) p
  have raw := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hp hD
    (transport z R B K i x p hR hK hB hi hz) (corrected_sharp_row z R B K i x p hR hK hB hi hz)
  have h1 : Γ ⊢[PRAAx] le one (R*R) := positive_product _ _ hR hR
  have h2 : Γ ⊢[PRAAx] le one E :=
    positive_product _ _ (positive_product _ _ (le_of_eq_add (d := num 47) (by ipra_ring)) h1)
      (le_trans h1 (le_add_right _ _))
  have cost : Γ ⊢[PRAAx] le (H*D+E*unit p) (T*unit p) :=
    le_congr (.eqRefl _) (by dsimp only [T,E]; unfold rowErrorNumerator; ipra_ring)
      (add_le_add_right (E*unit p)
        (le_trans hpay (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono h2 (le_refl (unit p))))))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hD) hD
    (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono cost (le_refl D))) raw

end LeanProofs.IPRA.Analysis.GaussianSineProductT4SharpRow
