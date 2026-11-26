import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherRows
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeTaylor
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeRow
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalParityPower

/-!
# The higher Barnes Taylor rows are the weighted Mercator terms

Multiplying the original relative step by k recovers the full
increment divided by the original Barnes base. At every degree j+3,
the powers of k cancel against the stored coefficient denominator,
leaving the original Mercator coefficient and the row weight k.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherRelative

open_ipra
open ComplexLogarithmRemainder (mul scale)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalHigherRows
  (coefficient previous degree coefficientDenominator powerDenominator
    degree_positive coefficient_denominator_positive power_denominator_positive)
open GaussianBarnesCanonicalRelativeStep (source relative numerator denominator denominator_positive)
open GaussianBarnesCanonicalRelativeTaylor (step recover_step)
open GaussianDominantPairAlgebra (radiusNumerator radiusPoint radius_represents radius_multiply radius_power radius_congr)
open GaussianEulerIncompleteFactorialDenominator (radius_rescale)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalHorner (qmul qmul_canonical ofGaussian ofGaussian_canonical ofGaussian_represents
  qmul_represents represents_rescale represents_congr positive_product canonical_unique)
open GaussianRationalMatrixFiniteSums (negative_as_minusOne)
open GaussianRationalMetric (qnegative)
open GaussianRationalParityPower (negative_power parity_succ)
open GaussianRationalPowerAlgebra (qmul_commutative power_product)
open GaussianRationalReciprocal (power powerF reciprocal)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_scale im_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem radius_product_native (a z : PTm n) :
    Γ ⊢[PRAAx] equal (mul (radiusNumerator a) z) (scale a z) := by
  apply equal_of_values <;> simp only [radiusNumerator,re_mul,im_mul,re_scale,im_scale,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

private theorem left_comm (a b c : PTm n) : Γ ⊢[PRAAx]
    qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative a b) (.eqRefl c)).eqTrans (qmul_associative b a c))

private theorem scale_step (h B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (radiusPoint k one) (step h B k) ≐ ofGaussian h B := by
  let D := B*k
  have hd := positive_product B k hB hk
  have prod := qmul_represents (radiusPoint k one) (step h B k) (radiusNumerator k) h one D
    (le_refl one) hd (radius_represents k one (le_refl one)) (ofGaussian_represents h D hd)
  exact canonical_unique _ _ (scale k h) D (qmul_canonical _ _) (ofGaussian_canonical _ _ hB) hd
    (represents_congr (.eqRefl _) (radius_product_native k h) (one_mul D) prod)
    (represents_rescale (ofGaussian h B) h B k (ofGaussian_represents h B hB))

theorem scaled_relative (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qmul (reciprocal (base z B k)) (ofGaussian h B) ≐ qmul (radiusPoint k one) (relative z h B k) := by
  let i := reciprocal (base z B k)
  let v := relative z h B k
  let w := radiusPoint k one
  let a := base z B k
  have vCanon := ofGaussian_canonical (numerator z h B k) (denominator z B k)
    (denominator_positive z R B k hs.andE₁)
  have inv := (qmul_commutative i a).eqTrans (GaussianBarnesCanonicalSecondDerivativeRow.reciprocal_base z R B k hs.andE₁)
  have unscaled : Γ ⊢[PRAAx] qmul i (step h B k) ≐ v :=
    (qmul_congr (.eqRefl i) (recover_step z h R B k H hs).eqSymm).eqTrans
      ((qmul_associative i a v).eqSymm.eqTrans
        ((qmul_congr inv (.eqRefl v)).eqTrans ((qmul_commutative _ v).eqTrans (qmul_one_right v vCanon))))
  exact (qmul_congr (.eqRefl i) (scale_step h B k hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁).eqSymm).eqTrans
    ((left_comm i w (step h B k)).eqTrans (qmul_congr (.eqRefl w) unscaled))

private theorem signed_power (a j : PTm n) : Γ ⊢[PRAAx]
    qnegative (power (qnegative a) (degree j)) ≐ qmul (parityPoint (previous j)) (power a (degree j)) := by
  let r := previous j
  let d := degree j
  let s := parityPoint d
  let p := power a d
  have sign : Γ ⊢[PRAAx] qnegative s ≐ parityPoint r :=
    (GaussianInverseBinomialRows.negative_congr (parity_succ r)).eqTrans
      (GaussianDeterminantSignTransport.negative_involution (parityPoint r)
        (ofGaussian_canonical _ _ (le_refl one)))
  exact (GaussianInverseBinomialRows.negative_congr (negative_power a d)).eqTrans
    ((negative_as_minusOne (qmul s p)).eqTrans
      ((qmul_associative _ s p).eqSymm.eqTrans
        (qmul_congr ((negative_as_minusOne s).eqSymm.eqTrans sign) (.eqRefl p))))

private theorem mercator_scalar (r : PTm n) : Γ ⊢[PRAAx]
    qmul (parityPoint r) (radiusPoint one (ConciseIPRA.PTm.succ r)) ≐ GaussianFiniteLogarithmPolynomial.coefficient r := by
  let d := ConciseIPRA.PTm.succ r
  let s := GaussianFiniteLogarithmPolynomial.signNumerator r
  let a := parityPoint r
  let b := radiusPoint one d
  have hd := zero_lt_succ (Γ := Γ) r
  have rep := qmul_represents b a (radiusNumerator one) s d one hd (le_refl one)
    (radius_represents one d hd) (ofGaussian_represents s one (le_refl one))
  have native : Γ ⊢[PRAAx] equal (mul (radiusNumerator one) s) s := by
    apply GaussianRootAlgebra.equal_trans (radius_product_native one s)
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring
  exact (qmul_commutative a b).eqTrans (canonical_unique _ _ s d (qmul_canonical _ _)
    (GaussianFiniteLogarithmPolynomial.coefficient_canonical r) hd
    (represents_congr (.eqRefl _) native ((mul_comm d one).eqTrans (one_mul d)) rep)
    (GaussianFiniteLogarithmPolynomial.coefficient_represents r))

private theorem weight (k j : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    qmul (radiusPoint one (coefficientDenominator k j)) (power (radiusPoint k one) (degree j)) ≐
      qmul (radiusPoint k one) (radiusPoint one (degree j)) := by
  let P := powerDenominator k j
  let d := degree j
  let E := coefficientDenominator k j
  have hE := coefficient_denominator_positive k j hk
  have hd := degree_positive (Γ := Γ) j
  have hp := power_denominator_positive k j hk
  have pwEq : Γ ⊢[PRAAx] power (radiusPoint k one) d ≐ radiusPoint (k*P) one :=
    (radius_power k one d (le_refl one)).eqTrans
      (radius_congr ((pw_succ k (previous j)).eqTrans (mul_comm P k)) (GaussianPolynomialPerturbation.one_power d))
  have unscaled := radius_rescale k d P hd hp
  exact (qmul_congr (.eqRefl _) pwEq).eqTrans
    ((radius_multiply one E (k*P) one hE (le_refl one)).eqTrans
      ((radius_congr (one_mul _) ((mul_comm E one).eqTrans (one_mul E))).eqTrans
        (unscaled.eqTrans
          ((radius_multiply k one one d (le_refl one) hd).eqTrans
            (radius_congr ((mul_comm k one).eqTrans (one_mul k)) (one_mul d))).eqSymm)))

theorem term_binding (z h R B k H j : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qmul (coefficient z B k j) (power (ofGaussian h B) (degree j)) ≐
      qmul (radiusPoint k one)
        (qmul (GaussianFiniteLogarithmPolynomial.coefficient (previous j)) (power (relative z h B k) (degree j))) := by
  let d := degree j
  let a := reciprocal (base z B k)
  let b := ofGaussian h B
  let v := relative z h B k
  let K := radiusPoint k one
  let S := parityPoint (previous j)
  let W := radiusPoint one (coefficientDenominator k j)
  let C := radiusPoint one d
  let P := power a d
  let Q := power b d
  let T := power v d
  have power_step : Γ ⊢[PRAAx] qmul P Q ≐ qmul (power K d) T :=
    (power_product a b d).eqSymm.eqTrans
      ((congrAp2 powerF (.eqRefl d) (scaled_relative z h R B k H hs)).eqTrans (power_product K v d))
  have pair : Γ ⊢[PRAAx] qmul (qmul P W) Q ≐ qmul (qmul K C) T :=
    (qmul_associative P W Q).eqTrans ((left_comm P W Q).eqTrans
      ((qmul_congr (.eqRefl W) power_step).eqTrans
        ((qmul_associative W (power K d) T).eqSymm.eqTrans
          (qmul_congr (weight k j hs.andE₁.andE₂.andE₁) (.eqRefl T)))))
  have attach : Γ ⊢[PRAAx] qmul S (qmul (qmul K C) T) ≐
      qmul K (qmul (GaussianFiniteLogarithmPolynomial.coefficient (previous j)) T) :=
    (qmul_congr (.eqRefl S) (qmul_associative K C T)).eqTrans
      ((left_comm S K (qmul C T)).eqTrans
        (qmul_congr (.eqRefl K) ((qmul_associative S C T).eqSymm.eqTrans
          (qmul_congr (mercator_scalar (previous j)) (.eqRefl T)))))
  exact (qmul_congr (qmul_congr (signed_power a j) (.eqRefl W)) (.eqRefl Q)).eqTrans
    ((qmul_congr (qmul_associative S P W) (.eqRefl Q)).eqTrans
      ((qmul_associative S (qmul P W) Q).eqTrans ((qmul_congr (.eqRefl S) pair).eqTrans attach)))

theorem actual_Barnes_higher_Mercator_term_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     let j := var 6
     source z h R B k H ⟶
       (qmul (coefficient z B k j) (power (ofGaussian h B) (degree j)) ≐ qmul (radiusPoint k one)
         (qmul (GaussianFiniteLogarithmPolynomial.coefficient (previous j)) (power (relative z h B k) (degree j))))) :=
  closeUniv 7 (.impI (term_binding _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherRelative
