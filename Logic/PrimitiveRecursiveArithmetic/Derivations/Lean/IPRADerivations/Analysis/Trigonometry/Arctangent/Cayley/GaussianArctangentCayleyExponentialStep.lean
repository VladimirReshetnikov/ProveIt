import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.GaussianArctangentCayleyStep
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Tails.GaussianGammaCanonicalTailExponential
import IPRADerivations.Analysis.Exponential.Estimates.Lipschitz.GaussianRationalUniformExponentialLipschitz
import IPRADerivations.Analysis.Exponential.FiniteSeries.GaussianScalarExponentialProductTail
import IPRADerivations.DiophantineNumberTheory.ResidueFacts

/-!
# One step of the finite arctangent exponential telescope

The two adjacent rows use the same literal exponential cutoff. The local
error is at most (128/M² + 2⁻ˢ), with no dependence on the grid index.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyExponentialStep

open_ipra
open ComplexLogarithmRemainder (normSq normSq_eval eval_re_code eval_im_code scale oneCode)
open GaussianArctangentCayleyStep (conjugateValue increment incrementCode local_defect)
open GaussianArctangentCayleyValues (numerator denominator denominator_positive exact_square_norm
  imaginaryCode imaginaryPoint)
open GaussianRationalHorner (canonical qzero qadd qmul ofGaussian_canonical ofGaussian_represents positive_product canonical_unique represents_congr represents_rescale qmul_represents)
open GaussianRationalReciprocal (qone conjugate norm_conjugate qone_bounded bound_congr
  qone_represents_scaled re_conjugate im_conjugate)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qnegative qnegative_represents
  qnegative_canonical)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_scale im_scale re_neg im_neg re_one im_one re_mul im_mul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same norm_from_distance_same)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianScalarExponentialProductTail (rectangleCutoff reserve growthExponent actual_scalar_product_dyadic)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianReconstructionRoots (distance_zero_iff distance_triangle)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def sample (P s : PTm n) : PTm n := scalarSum P (rectangleCutoff two s)
def row (M j s P : PTm n) : PTm n := qmul (sample P s) (conjugateValue M j)

ipra_subst sample [rectangleCutoff, reserve, growthExponent]

ipra_subst row [conjugateValue, numerator, denominator]

theorem sample_canonical (P s : PTm n) : Γ ⊢[PRAAx] canonical (sample P s) :=
  GaussianRationalFiniteSum.sum_canonical scalarBody (succ (rectangleCutoff two s)) P

theorem row_canonical (M j s P : PTm n) : Γ ⊢[PRAAx] canonical (row M j s P) :=
  GaussianRationalHorner.qmul_canonical _ _

theorem conjugate_unit_bound (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (conjugateValue M j) one one := by
  let d := denominator M j
  let a := conjugate (numerator M j)
  have hd := denominator_positive M j hM
  have square : Γ ⊢[PRAAx] normSq a ≐ d*d :=
    (norm_conjugate (numerator M j)).eqTrans (exact_square_norm M j)
  apply bounded_of_cleared _ a d one one hd (le_refl _) (ofGaussian_represents _ _ hd)
  exact le_congr (by ipra_ring) (by ipra_ring) (le_congr square.eqSymm (.eqRefl _) (le_refl (d*d)))

theorem conjugate_left_endpoint (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] conjugateValue M zero ≐ qone := by
  let d := denominator M zero
  have hd := denominator_positive M zero hM
  have e : Γ ⊢[PRAAx] equal (conjugate (numerator M zero)) (scale d oneCode) := by
    dsimp only [d]
    apply equal_of_values <;>
      simp only [re_conjugate, im_conjugate, numerator, denominator, eval_re_code, eval_im_code,
        ZT.toZ_sub, ZT.toZ_ofNat, re_scale, im_scale, re_one, im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ d (ofGaussian_canonical _ _ hd) (ofGaussian_canonical _ _ (le_refl one))
    hd (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hd)) (qone_represents_scaled d)

theorem conjugate_right_endpoint (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] conjugateValue M M ≐ qnegative imaginaryPoint := by
  let d := denominator M M
  have hd := denominator_positive M M hM
  have e : Γ ⊢[PRAAx] equal (conjugate (numerator M M)) (scale d (ComplexLogarithmRemainder.neg imaginaryCode)) := by
    dsimp only [d]
    apply equal_of_values <;>
      simp only [re_conjugate, im_conjugate, numerator, denominator, imaginaryCode, eval_re_code, eval_im_code,
        ZT.toZ_sub, ZT.toZ_ofNat, re_scale, im_scale, re_neg, im_neg] <;>
      ipra_simps <;> ring
  have hr := qnegative_represents (Γ := Γ) (imaginaryPoint : PTm n) imaginaryCode one (ofGaussian_represents _ _ (le_refl one))
  have rep := represents_congr (.eqRefl _) (equal_refl _) (one_mul d)
    (represents_rescale _ _ one d hr)
  exact canonical_unique _ _ _ d (ofGaussian_canonical _ _ hd) (qnegative_canonical _) hd
    (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hd)) rep

theorem right_inverse_endpoint (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (conjugateValue M M) imaginaryPoint ≐ qone := by
  have hp : Γ ⊢[PRAAx] GaussianRationalHorner.represents imaginaryPoint imaginaryCode one :=
    ofGaussian_represents _ _ (le_refl one)
  have hn := qnegative_represents _ _ _ hp
  have rep := qmul_represents _ _ _ _ one one (le_refl one) (le_refl one) hn hp
  have e : Γ ⊢[PRAAx] equal
      (ComplexLogarithmRemainder.mul (ComplexLogarithmRemainder.neg imaginaryCode) imaginaryCode) (scale one oneCode) := by
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_neg, im_neg, imaginaryCode, eval_re_code, eval_im_code,
        ZT.toZ_ofNat, re_scale, im_scale, re_one, im_one] <;>
      ipra_simps <;> ring
  exact (qmul_congr (conjugate_right_endpoint M hM) (.eqRefl _)).eqTrans
    (canonical_unique _ _ _ one (GaussianRationalHorner.qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one))
      (le_refl one) (represents_congr (.eqRefl _) e (one_mul _) rep) (qone_represents_scaled one))

theorem increment_bound (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (increment M j) two M := by
  let d := denominator M j
  have hd := denominator_positive M j hM
  have square : Γ ⊢[PRAAx] normSq (incrementCode M) ≐ (two*M)*(two*M) := by
    apply deriveNat
    rw [normSq_eval]
    simp only [incrementCode, eval_re_code, eval_im_code, ZT.toZ_ofNat]
    ipra_simps
    ring
  have lower : Γ ⊢[PRAAx] le (M*M) d := le_add_right _ _
  have bound := le_mul_mono (le_refl (two*two)) (le_mul_mono lower lower)
  apply bounded_of_cleared _ _ d two M hd hM (ofGaussian_represents _ _ hd)
  exact le_congr ((by ipra_ring : Γ ⊢[PRAAx] (two*two)*((M*M)*(M*M)) ≐
    (M*M)*((two*M)*(two*M))).eqTrans (congrMul (.eqRefl _) square.eqSymm)) (.eqRefl _) bound

theorem sample_bound (P s : PTm n) (hP : Γ ⊢[PRAAx] bounded P two one) :
    Γ ⊢[PRAAx] bounded (sample P s) (num 19) one := by
  let K := rectangleCutoff two s
  have h0 : Γ ⊢[PRAAx] bounded (qzero : PTm n) two one :=
    GaussianMonicResidualRadius.zero_bounded _ _ (le_refl _)
  have dp := (distance_zero_iff P two one (le_refl one)).iffMpr hP
  have raw := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz P qzero two two one K
    (le_refl one) hP h0 dp
  have d : Γ ⊢[PRAAx] distanceBounded (sample P s) qone (num 18) one :=
    distance_congr (.eqRefl _) (GaussianGammaCanonicalTailExponential.scalar_zero_point K)
      ((congrMul (DiophantineNumberTheory.ResidueFacts.pw_two (num 3)) (.eqRefl _)).eqTrans (by ipra_ring))
      (.eqRefl _) raw
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (norm_from_distance_same (le_refl one) d qone_bounded)

theorem sample_zero (s : PTm n) : Γ ⊢[PRAAx] sample qzero s ≐ qone :=
  GaussianGammaCanonicalTailExponential.scalar_zero_point (rectangleCutoff two s)

private theorem cutoff_positive (s : PTm n) : Γ ⊢[PRAAx] le one (rectangleCutoff two s) := by
  unfold rectangleCutoff reserve growthExponent
  ipra_le 16*𝔞 s+831

private theorem right_multiply_unit_distance (u v c A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] bounded c one one) (h : Γ ⊢[PRAAx] distanceBounded u v A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul u c) (qmul v c) A B :=
  distance_congr (qmul_commutative c u) (qmul_commutative c v) (one_mul A) (.eqRefl _)
    (multiply_distance c u v one A B hB hc h)

theorem local_exponential_step (M j s P : PTm n) (hM : Γ ⊢[PRAAx] le two M)
    (hP : Γ ⊢[PRAAx] bounded P two one) :
    Γ ⊢[PRAAx] distanceBounded (row M (succ j) s (qadd P (increment M j))) (row M j s P)
      (num 128*pw two s+M*M) (M*M*pw two s) := by
  let I := increment M j
  let D := conjugateValue M (succ j)
  let A := sample P s
  let U := sample I s
  let V := qadd qone I
  have oneTwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hp := le_trans oneTwo hM
  have hm := positive_product M M hp hp
  have hs := GaussianFactorBudget.power_positive (Γ := Γ) two s oneTwo
  have hi := increment_bound M j hp
  have hiCan : Γ ⊢[PRAAx] canonical I :=
    ofGaussian_canonical _ _ (denominator_positive M j hp)
  have hD := conjugate_unit_bound M (succ j) hp
  have hA := sample_bound P s hP
  have hSmall : Γ ⊢[PRAAx] bounded I two one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hp (le_refl one)
      (le_mul_mono (le_refl two) hp) hi
  have hProduct := distance_symmetric _ _ _ _ hs (actual_scalar_product_dyadic P I two s oneTwo hP hSmall)
  have hStart : Γ ⊢[PRAAx] distanceBounded (row M (succ j) s (qadd P I))
      (qmul A (qmul U D)) one (pw two s) :=
    distance_congr (.eqRefl _) (qmul_associative A U D) (.eqRefl _) (.eqRefl _)
      (right_multiply_unit_distance _ _ D _ _ hs hD hProduct)
  have hLinear : Γ ⊢[PRAAx] distanceBounded U V (two*two) (M*M) :=
    GaussianExponentialLinearRemainder.original_finite_linear_remainder I two M _ hp hM hi hiCan (cutoff_positive s)
  have hMiddle := multiply_distance A _ _ _ _ _ hm hA
    (right_multiply_unit_distance U V D _ _ hm hD hLinear)
  have hEnd := multiply_distance A _ _ _ _ _ hm hA (local_defect M j hp)
  have hMesh : Γ ⊢[PRAAx] distanceBounded (qmul A (qmul U D)) (row M j s P) (num 128) (M*M) :=
    distance_radius_mono _ _ _ _ _ _ hm hm
      (by ipra_le 14*𝔞 (M*M)) (distance_triangle_same _ _ _ _ _ _ hm hMiddle hEnd)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (distance_triangle _ _ _ _ _ _ _ hs hm hStart hMesh)

theorem actual_original_arctangent_exponential_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le two (var 0) ⟶ bounded (var 3) two one ⟶
      distanceBounded (row (var 0) (succ (var 1)) (var 2) (qadd (var 3) (increment (var 0) (var 1))))
        (row (var 0) (var 1) (var 2) (var 3)) (num 128*pw two (var 2)+var 0*var 0)
        (var 0*var 0*pw two (var 2))) :=
  closeUniv 4 (.impI (.impI (local_exponential_step _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyExponentialStep
