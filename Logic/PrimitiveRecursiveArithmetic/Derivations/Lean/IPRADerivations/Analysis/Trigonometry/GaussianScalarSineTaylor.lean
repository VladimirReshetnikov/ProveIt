import IPRADerivations.Analysis.Exponential.FiniteSeries.GaussianScalarExponentialOddTaylor
import IPRADerivations.Analysis.Trigonometry.GaussianNamedSineFromExponential
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod

/-!
# Exact signed sine Taylor polynomial

At every finite even cutoff, multiplying the difference of the same
scalar exponential at `i*z` and `-i*z` by the original sine multiplier
gives the alternating factorial sum in `z`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarSineTaylor

open_ipra
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianNamedSineFromExponential (multiplier)
open GaussianScalarExponentialOddTaylor (scalarTerm oddBody oddSum odd_taylor_identity)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalHorner (qmul qadd canonical_unique represents_congr represents_rescale ofGaussian_canonical
  ofGaussian_represents qadd_represents qadd_canonical qmul_canonical)
open GaussianRationalMetric (qsub qnegative qnegative_represents qnegative_canonical)
open GaussianRationalReciprocal (qone power powerF power_succ)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalPowerAlgebra (power_two power_composition power_product qmul_commutative)
open GaussianRationalParityPower (minus_one_power)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_congr_bounded sum_multiply)
open GaussianReciprocalHorner (qmul_associative)
open GaussianInverseBinomialRows (negative_congr negative_product)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_add im_add re_scale im_scale re_neg im_neg re_one im_one)
open ComplexLogarithmRemainder (code oneCode scale eval_re_code eval_im_code)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedTerm (z j : PTm n) : PTm n := qmul (parityPoint j) (scalarTerm z (succ (two*j)))
def signedBody : PTm 2 := signedTerm (var 1) (var 0)
def signedSum (z K : PTm n) : PTm n := sum signedBody K z

ipra_subst signedSum

private theorem signed_body_at (z j : PTm n) : inst2 signedBody j z = signedTerm z j := by
  simp [signedBody, signedTerm, scalarTerm, inst2]

theorem signed_sum_canonical (z K : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (signedSum z K) :=
  GaussianRationalFiniteSum.sum_canonical _ _ _

private theorem imaginary_square_signed :
    Γ ⊢[PRAAx] qmul (imaginaryPoint : PTm n) imaginaryPoint ≐ GaussianRationalMatrixFiniteSums.minusOne := by
  have en : Γ ⊢[PRAAx] equal GaussianArctangentExponentialPeriod.minusOneCode (ComplexLogarithmRemainder.neg oneCode) := by
    apply equal_of_values <;>
      simp only [GaussianArctangentExponentialPeriod.minusOneCode, eval_re_code, eval_im_code,
        ZT.toZ_sub, ZT.toZ_ofNat, re_neg, im_neg, re_one, im_one] <;>
      ipra_simps <;> ring
  have he := canonical_unique GaussianArctangentExponentialPeriod.minusOne (qnegative qone) _ one
    (ofGaussian_canonical _ _ (le_refl one)) (qnegative_canonical _) (le_refl one)
    (represents_congr (.eqRefl _) en (.eqRefl _) (ofGaussian_represents _ _ (le_refl one)))
    (qnegative_represents _ _ _ (ofGaussian_represents _ _ (le_refl one)))
  exact GaussianArctangentExponentialPeriod.imaginary_square.eqTrans he

private theorem imaginary_odd_power (j : PTm n) :
    Γ ⊢[PRAAx] power (imaginaryPoint : PTm n) (succ (two*j)) ≐ qmul imaginaryPoint (parityPoint j) := by
  let i := (imaginaryPoint : PTm n)
  have square := (power_two (Γ := Γ) i (ofGaussian_canonical _ _ (le_refl one))).eqTrans imaginary_square_signed
  have even := (power_composition (Γ := Γ) i two j).eqSymm.eqTrans
    ((congrAp2 powerF (.eqRefl j) square).eqTrans (minus_one_power j))
  exact (power_succ i (two*j)).eqTrans ((qmul_congr even (.eqRefl _)).eqTrans (qmul_commutative _ _))

private theorem negative_i_times_i :
    Γ ⊢[PRAAx] qmul (qnegative (imaginaryPoint : PTm n)) imaginaryPoint ≐ qone :=
  (negative_product imaginaryPoint imaginaryPoint).eqSymm.eqTrans
    ((negative_congr imaginary_square_signed).eqTrans (GaussianDeterminantSignTransport.negative_involution _ qone_canonical))

private theorem twice_multiplier : Γ ⊢[PRAAx] qadd (multiplier : PTm n) multiplier ≐ qnegative imaginaryPoint := by
  let a := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have hd : Γ ⊢[PRAAx] le one two := le_succ_self one
  have ha := ofGaussian_represents (Γ := Γ) a two hd
  have sumRep := qadd_represents _ _ a a two hd ha ha
  have negRep := qnegative_represents (Γ := Γ) imaginaryPoint imaginaryCode one (ofGaussian_represents _ _ (le_refl one))
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.add a a) (scale two a) := by
    apply equal_of_values <;> simp only [re_add, im_add, re_scale, im_scale] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ two (qadd_canonical _ _) (qnegative_canonical _) hd
    (represents_congr (.eqRefl _) e (.eqRefl _) sumRep)
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul two) (represents_rescale _ _ _ _ negRep))

private theorem combine_multiplier (v : PTm n) :
    Γ ⊢[PRAAx] qmul multiplier (qadd v v) ≐ qmul (qnegative imaginaryPoint) v :=
  (GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
    ((GaussianRationalPolynomialBuffers.distribute_right _ _ _).eqSymm.eqTrans
      (qmul_congr twice_multiplier (.eqRefl _)))

private theorem swap_inner (a b c : PTm n) :
    Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a c))

private theorem scale_odd_term (z j : PTm n) :
    Γ ⊢[PRAAx] qmul (qnegative imaginaryPoint) (scalarTerm (qmul imaginaryPoint z) (succ (two*j))) ≐
      signedTerm z j := by
  let i := (imaginaryPoint : PTm n)
  let d := succ (two*j)
  let a := GaussianRationalPolynomialExponential.inverseFactorial d
  let p := parityPoint j
  let w := power z d
  have raw : Γ ⊢[PRAAx] power (qmul i z) d ≐ qmul i (qmul p w) :=
    (power_product i z d).eqTrans
      ((qmul_congr (imaginary_odd_power j) (.eqRefl w)).eqTrans (qmul_associative i p w))
  have arrange : Γ ⊢[PRAAx] scalarTerm (qmul i z) d ≐ qmul i (qmul p (qmul a w)) :=
    (qmul_congr (.eqRefl a) raw).eqTrans
      ((swap_inner a i (qmul p w)).eqTrans (qmul_congr (.eqRefl i) (swap_inner a p w)))
  exact (qmul_congr (.eqRefl _) arrange).eqTrans
    ((qmul_associative (qnegative i) i (signedTerm z j)).eqSymm.eqTrans
      ((qmul_congr negative_i_times_i (.eqRefl _)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (qmul_canonical _ _))))

private theorem scale_odd_sum (z K : PTm n) :
    Γ ⊢[PRAAx] qmul (qnegative imaginaryPoint) (oddSum (qmul imaginaryPoint z) K) ≐ signedSum z K := by
  let i := (imaginaryPoint : PTm n)
  let q := qmul i z
  refine (sum_multiply oddBody (qnegative i) K q).eqSymm.eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded (multiplyBody oddBody) signedBody K (pairT (qnegative i) q) z (.allI (.impI ?_)))
  let C := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have e := multiply_body_at (Γ := C) oddBody (qnegative imaginaryPoint) (var 0) (qmul imaginaryPoint (Syn.shift z))
  simpa only [GaussianRationalFiniteSum.termsEqual, Syn.shift, C, i, q, GaussianRationalHorner.subst_qmul,
    GaussianRationalMetric.subst_qnegative, GaussianArctangentCayleyValues.imaginaryPoint,
    GaussianArctangentCayleyValues.imaginaryCode, GaussianRationalHorner.subst_ofGaussian, ComplexLogarithmRemainder.subst_code,
    subst_pairT, ZT.subst_ofNat, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    e.eqTrans (by
      rw [GaussianScalarExponentialOddTaylor.odd_body_at, signed_body_at]
      exact scale_odd_term (Syn.shift z) (var 0))

theorem finite_sine_taylor (z K : PTm n) : Γ ⊢[PRAAx]
    qmul multiplier (qsub (scalarSum (qmul imaginaryPoint z) (two*K))
      (scalarSum (qnegative (qmul imaginaryPoint z)) (two*K))) ≐ signedSum z K :=
  (qmul_congr (.eqRefl _) (odd_taylor_identity (qmul imaginaryPoint z) K)).eqTrans
    ((combine_multiplier (oddSum (qmul imaginaryPoint z) K)).eqTrans (scale_odd_sum z K))

theorem actual_finite_signed_sine_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qmul multiplier (qsub (scalarSum (qmul imaginaryPoint (var 0)) (two*var 1))
      (scalarSum (qnegative (qmul imaginaryPoint (var 0))) (two*var 1))) ≐ signedSum (var 0) (var 1)) :=
  closeUniv 2 (finite_sine_taylor _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarSineTaylor
