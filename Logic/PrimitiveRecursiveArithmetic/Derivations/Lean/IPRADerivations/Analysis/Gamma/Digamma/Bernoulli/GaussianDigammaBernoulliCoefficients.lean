import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliRecurrence
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSignedLowerAlgebra

/-!
# Literal digamma Bernoulli correction terms

The signed mean of the centered Bernoulli polynomial times the
reciprocal primitive gives the original digamma coefficient
b_(2m+2)/(2m+2) at the even inverse power. The coefficients are
constructed from the original cleared Bernoulli coefficient table.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliCoefficients

open_ipra
open BernoulliBounds (bden bden_pos bint zint toZ_zint)
open GaussianDigammaBernoulliRecurrence (exponent weightedPrimitive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product qmul)
open GaussianStirlingAllOrderCenteredBernoulli (factor)
open GaussianStirlingAllOrderPanelDerivative (signedMean mean_value mean_den_positive)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderSignedLowerAlgebra (orientationCode orientationPoint)
open GaussianStirlingAllOrderTruncationCoefficients (sign)
open RationalArithmetic (multiply multiply_guard negative negative_guard)
open RationalFiniteSum (canonical_equal)
open RationalGaussianEmbedding (embed embed_multiply embed_negative)
open RationalGaussianRealPart (embed_congr)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalRepresentations (represents_multiply represents_negative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientNumerator (m : ℕ) : ℤ := ((2*m+1).factorial : ℤ)*bint (2*m+2) 0

def coefficient (m : ℕ) : PTm n := normalize (zint (coefficientNumerator m)) (num (bden (2*m+2)))

def inversePower (m : ℕ) (A B : PTm n) : PTm n := fraction (power (2*m+2) B) (power (2*m+2) A)

def correction (m : ℕ) (A B : PTm n) : PTm n := embed (multiply (coefficient m) (inversePower m A B))

ipra_subst correction [coefficient, inversePower, power, zint]

theorem bernoulli_coefficient (m : ℕ) :
    (coefficientNumerator m : ℚ) / (bden (2*m+2) : ℚ) =
      (((2*m+2).factorial : ℚ)*BernoulliCoefficients.bc (2*m+2) 0)/(2*m+2) := by
  have hd : (bden (2*m+2) : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (bden_pos _)
  have hm : (2*(m : ℚ)+2) ≠ 0 := by positivity
  simp only [coefficientNumerator,Int.cast_mul,Int.cast_natCast,BernoulliBounds.bint_eq,Fin.val_zero]
  rw [Nat.factorial_succ (2*m+1)]
  push_cast
  field_simp
  ring

private theorem sign_mean (m : ℕ) :
    sign m*(-factor (m+1)*bint (2*m+2) 0) = coefficientNumerator m*((2*m+2 : ℕ) : ℤ) := by
  have h : (-1 : ℤ)^m*(-1 : ℤ)^m=1 := by rw [← pow_add,← two_mul,pow_mul]; norm_num
  unfold sign factor coefficientNumerator
  rw [show 2*(m+1)=2*m+2 by omega, Nat.factorial_succ (2*m+1),pow_succ]
  push_cast
  linear_combination (((2*m+1).factorial : ℤ)*bint (2*m+2) 0*(2*(m : ℤ)+2))*h

theorem sign_step (m : ℕ) : Γ ⊢[PRAAx] (orientationPoint (m+1) : PTm n) ≐
    GaussianRationalMetric.qnegative (orientationPoint m) := by
  have v : sign (m+1) = -sign m := by unfold sign; rw [pow_succ]; ring
  have h : Γ ⊢[PRAAx] (orientationCode (m+1) : PTm n) ≐ negative (orientationCode m) := by
    let e := normalize_preserves_value (Γ := Γ)
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ (le_refl one)) (negative_guard _)
      (e _ _ (le_refl one)) (represents_negative _ _ _ (e _ _ (le_refl one))) (le_refl one) (le_refl one)
    apply ZT.derive
    simp [ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,toZ_zint,v]
  exact (embed_congr h).eqTrans (embed_negative _)

private theorem scalar_correction (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] multiply (orientationCode m) (multiply (signedMean (m+1)) (primitive (exponent m) A B)) ≐
      multiply (coefficient m) (inversePower m A B) := by
  let j := 2*m+2
  let D : PTm n := num (bden j)
  let E : PTm n := num j
  let U := power j B
  let V := power j A
  have hD : Γ ⊢[PRAAx] le one D := Foundations.NumeralPrimes.num_le (bden_pos j)
  have hE : Γ ⊢[PRAAx] le one E := Foundations.NumeralPrimes.num_le (by unfold j; omega : 1≤j)
  have hV := GaussianFactorBudget.power_positive A (num j) hA
  have hEV := positive_product _ _ hE hV
  have he : exponent m-1 = j := by unfold exponent j; omega
  have pv : Γ ⊢[PRAAx] RationalArithmetic.represents (primitive (exponent m) A B) (ZT.ofNat U) (E*V) := by
    unfold primitive
    rw [he]
    exact fraction_represents _ _ hEV
  have value := represents_multiply _ _ _ _ _ _
    (normalize_preserves_value (Γ := Γ) (zint (sign m)) one (le_refl one))
    (represents_multiply _ _ _ _ _ _ (mean_value (m+1)) pv)
  have literal := represents_multiply _ _ _ _ _ _
    (normalize_preserves_value (Γ := Γ) (zint (coefficientNumerator m)) D hD)
    (fraction_represents U V hV)
  apply canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (multiply_guard _ _) value literal
    (positive_product _ _ (le_refl one) (positive_product _ _ (mean_den_positive _) hEV))
    (positive_product _ _ hD hV)
  apply ZT.derive
  have s : (sign m : Groth (Q Γ))*(-(factor (m+1) : Groth (Q Γ))*(bint j 0 : Groth (Q Γ))) =
      (coefficientNumerator m : Groth (Q Γ))*(j : Groth (Q Γ)) := by
    have t := congrArg (fun a : ℤ => (a : Groth (Q Γ))) (sign_mean m)
    simpa only [Int.cast_mul,Int.cast_neg,Int.cast_natCast,j] using t
  have hj : 2*(m+1) = j := by unfold j; omega
  simp only [GaussianStirlingAllOrderPanelDerivative.meanNumerator,ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,
    Int.cast_mul,Int.cast_neg,IPRA.Q.mk_mul,map_mul,IPRA.Q.mk_one,map_one,hj,D,E,IPRA.Q.mk_num,map_natCast]
  linear_combination (Groth.ι (Q.mk Γ U)*Groth.ι (Q.mk Γ V)*(bden j : Groth (Q Γ)))*s

theorem actual_correction (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] qmul (orientationPoint m) (weightedPrimitive m A B) ≐ correction m A B :=
  (embed_multiply _ _).eqSymm.eqTrans (embed_congr (scalar_correction m A B hA))

theorem orientation_square (m : ℕ) : Γ ⊢[PRAAx]
    qmul (orientationPoint m) (orientationPoint m : PTm n) ≐ GaussianRationalSyntheticDivision.qone := by
  let q : PTm n := orientationCode m
  have h := positive_product (Γ := Γ) one one (le_refl one) (le_refl one)
  have value := normalize_preserves_value (Γ := Γ) (zint (sign m)) one (le_refl one)
  have e : Γ ⊢[PRAAx] multiply q q ≐ fraction one one := by
    apply canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (normalize_well_formed _ _ (le_refl one))
      (represents_multiply _ _ _ _ _ _ value value) (fraction_represents _ _ (le_refl one)) h (le_refl one)
    apply ZT.derive
    have s : sign m*sign m=1 := by unfold sign; rw [← pow_add,← two_mul,pow_mul]; norm_num
    have j := congrArg (fun a : ℤ => (a : Groth (Q Γ))) s
    simpa only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,IPRA.Q.mk_one,map_one,Int.cast_mul,
      Int.cast_one,IPRA.Q.mk_mul,map_mul,_root_.mul_one] using j
  exact (embed_multiply q q).eqSymm.eqTrans ((embed_congr e).eqTrans RationalGaussianEmbedding.embed_one)

theorem oriented_correction (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] qmul (orientationPoint m) (correction m A B) ≐ weightedPrimitive m A B := by
  let c := weightedPrimitive m A B
  have h : Γ ⊢[PRAAx] GaussianRationalHorner.canonical c := RationalGaussianEmbedding.embed_canonical _
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (actual_correction m A B hA).eqSymm).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (orientation_square m) (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right c h))))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliCoefficients
