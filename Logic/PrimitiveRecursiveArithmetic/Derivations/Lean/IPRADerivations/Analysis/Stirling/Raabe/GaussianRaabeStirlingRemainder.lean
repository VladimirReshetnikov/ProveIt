import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeStirlingCell
import IPRADerivations.Analysis.Stirling.GaussianStirlingExpansionFirstOrder

/-!
# The original sampled log-Gamma and the elementary Raabe term

The real Stirling theorem bounds the original named remainder on
arguments at least one. Fold the original name back into the same
log-Gamma and logarithm observations used by the finite Raabe grid.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeStirlingRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData multiplyModulus multiply_at sum_distance)
open GaussianNameEquivalence (cross_at cross_symm cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianRaabeStirlingCell (elementary elementary_at half)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qadd_canonical qmul qmul_canonical qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_sum)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qmul_congr qzero_add)
open GaussianStirlingMultiplicativeAlgebra (normalizationF normalizationData normalizationSumF normalizationSumData
  normalization_sum_regular normalization_regular logarithmic_cancellation remainderF remainderData remainder_regular)
open GaussianStirlingNames (logGammaF logGammaData log_gamma_regular logXF logXData productF productData product_regular)
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "CF" => GaussianStirlingConstant.nameF
local notation "CD" => GaussianStirlingConstant.nameData
local notation "SF" => GaussianStirlingMultiplicativeAlgebra.sumF
local notation "SD" => GaussianStirlingMultiplicativeAlgebra.sumData

def constantSample (p w : PTm n) : PTm n := ap2 CF p (CD w)
def model (p A D w : PTm n) : PTm n := qadd (elementary p A D) (constantSample p w)
def numerator (p A D : PTm n) : PTm n := two*D*unit p+(num 18+two*A)*A
def denominator (p A : PTm n) : PTm n := A*unit p

@[simp] theorem subst_constantSample {m : ℕ} (σ : Fin n → PTm m) (p w : PTm n) :
    Syn.subst σ (constantSample p w) = constantSample (Syn.subst σ p) (Syn.subst σ w) := by simp [constantSample]

@[simp] theorem subst_model {m : ℕ} (σ : Fin n → PTm m) (p A D w : PTm n) :
    Syn.subst σ (model p A D w) = model (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ w) := by
  simp [model]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p A D : PTm n) :
    Syn.subst σ (numerator p A D) = numerator (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [numerator,two,one]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p A : PTm n) :
    Syn.subst σ (denominator p A) = denominator (Syn.subst σ p) (Syn.subst σ A) := by simp [denominator]

private theorem divide_at_le_one (A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (fraction A D) A one :=
  GaussianEulerExponentCompactBounds.fraction_bound A D A hD
    (le_congr (one_mul A) (mul_comm D A) (mul_le_mul_right A hD))

private theorem offset_bound (A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (GaussianStirlingNames.offset A D) (A+one) one := by
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  exact GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
    (divide_at_le_one A D hD)
    (bounded_negative _ _ _ (le_refl one) (divide_at_le_one one two h2))

private theorem product_error (p A D : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingNames.source A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData A D))
      (qmul (GaussianStirlingNames.offset A D) (sample p A D)) (two*(A+one)) (unit p) := by
  let z := GaussianStirlingNames.offset A D
  let y := logXData A D
  let k := GaussianFastValueCut.exponent (multiplyModulus constantF logXF z y) p
  let U := unit p
  let V := unit k
  let h := ap2 logXF k y
  let l := sample p A D
  have hp := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) k
  have grow : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have e := GaussianHarmonicLogarithmName.cross_original A D hs
  have raw := cross_at logXF GaussianPositiveRationalLogarithm.logF y
    (GaussianPositiveRationalLogarithm.data A D) k p (cross_symm _ _ _ _ e)
  have rel : Γ ⊢[PRAAx] distanceBounded h l two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hv hp) hp
      (by change Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)); ipra_le 𝔞(U)*sl grow) raw
  have read : Γ ⊢[PRAAx] ap2 productF p (productData A D) ≐ qmul z h :=
    (multiply_at constantF logXF z y p).eqTrans
      ((GaussianNameArithmetic.recode_congr (qmul_congr (constant_at k z) (.eqRefl h))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))
  exact distance_congr read.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance z h l (A+one) two U hp (offset_bound A D hs.andE₂) rel)

private theorem normalization_error (p A D w : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianStirlingNames.source A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 normalizationF p (normalizationData A D w))
      (model p A D w) (num 11+two*A) (unit p) := by
  let x := fraction A D
  let C := constantSample p w
  let t := qmul (GaussianStirlingNames.offset A D) (sample p A D)
  let v := ap2 productF p (productData A D)
  let f := ap2 normalizationF p (normalizationData A D w)
  let z := ap2 normalizationSumF p (normalizationSumData A D w)
  have hp := unit_positive (Γ := Γ) p
  have hC := GaussianStirlingConstant.name_regular (Γ := Γ) w
  have hx := constant_regular (Γ := Γ) x
  have e₀ : Γ ⊢[PRAAx] distanceBounded f (qsub z x) (num 6) (unit p) :=
    distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p x)) (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifference.sample_error normalizationSumF constantF (normalizationSumData A D w) x p
        (normalization_sum_regular A D w hs) hx)
  have e₁ := add_sample_error CF productF (CD w) (productData A D) p hC (product_regular A D hs)
  have e₂ := sum_distance C C v t _ _ _ hp (distance_refl_zero C _ hp) (product_error p A D hs)
  have total := distance_triangle_same f (qsub z x) (qsub (qadd C t) x) _ _ (unit p) hp e₀
    (GaussianNamedDifference.difference_distance z (qadd C t) x x _ _ _ hp
      (distance_triangle_same z (qadd C v) (qadd C t) _ _ (unit p) hp e₁ e₂) (distance_refl_zero x _ hp))
  have eq : Γ ⊢[PRAAx] qsub (qadd C t) x ≐ model p A D w :=
    (GaussianRationalSumAlgebra.qadd_associative C t (qnegative x)).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative C (qsub t x)).eqTrans
        (qadd_congr (elementary_at p A D).eqSymm (.eqRefl C)))
  exact distance_congr (.eqRefl _) eq (by unfold three; ipra_ring) (.eqRefl _) total

private theorem remainder_bound (p A D w : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianStirlingNames.source A D) (hDA : Γ ⊢[PRAAx] le D A) :
    Γ ⊢[PRAAx] bounded (ap2 remainderF p (remainderData A D w)) (two*D*unit p+two*A) (A*unit p) := by
  let U := unit p
  let z := ap2 remainderF p (remainderData A D w)
  let q := GaussianStirlingRationalTelescopers.upperValue A D
  have hU := unit_positive (Γ := Γ) p
  have hAU := positive_product _ _ hs.andE₁ hU
  have hAA := positive_product _ _ hs.andE₁ hs.andE₁
  have h12 := GaussianStirlingRationalTelescopers.upper_den_positive A hs.andE₁
  have pD := (pw_succ (Γ := Γ) D one).eqTrans (congrMul (pw_one D) (.eqRefl D))
  have pA := (pw_succ (Γ := Γ) A one).eqTrans (congrMul (pw_one A) (.eqRefl A))
  have read : Γ ⊢[PRAAx] ap2 constantF p (GaussianStirlingExpansionFiniteError.logPolynomial 1 A D) ≐ q :=
    (constant_at _ _).eqTrans (GaussianStirlingExpansionFirstOrder.first_log_polynomial A D hs.andE₁)
  have near : Γ ⊢[PRAAx] distanceBounded z q (D*D*U*U+(A*A)*(U+U)) (A*A*U*U) :=
    distance_congr (.eqRefl _) read
      (congrAdd (congrMul (congrMul ((one_mul _).eqTrans pD) (.eqRefl U)) (.eqRefl U))
        (congrMul pA (.eqRefl _)))
      (congrMul (congrMul pA (.eqRefl U)) (.eqRefl U))
      (GaussianStirlingExpansionFirstOrder.log_error_at p p A D w hs hDA)
  have nearer : Γ ⊢[PRAAx] distanceBounded z q (D*U+two*A) (A*U) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hAA hU) hU) hAU
      (by
        change Γ ⊢[PRAAx] le ((D*D*U*U+(A*A)*(U+U))*(A*U)) ((D*U+two*A)*(A*A*U*U))
        ipra_le 𝔞(D*A*U*U*U)*sl hDA) near
  have upper : Γ ⊢[PRAAx] bounded q (D*U) (A*U) := by
    have base : Γ ⊢[PRAAx] bounded q D (num 12*A) :=
      bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point D (num 12*A) h12).eqSymm
        (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded D (num 12*A) h12)
    exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ h12 hAU
      (by ipra_le 11*𝔞(D)*𝔞(A)*𝔞(U)) base
  have tail := (GaussianReconstructionRoots.distance_zero_iff q _ _ hAU).iffMpr upper
  exact (GaussianReconstructionRoots.distance_zero_iff z _ _ hAU).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same z q qzero _ _ _ hAU nearer tail))

theorem sample_error (p A D w : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logGammaF p (logGammaData A D)) (model p A D w)
      (numerator p A D) (denominator p A) := by
  let U := unit p
  let g := ap2 logGammaF p (logGammaData A D)
  let gd := logGammaData A D
  let yd := SD A D w
  let y := ap2 SF p yd
  let r := ap2 remainderF p (remainderData A D w)
  let t := ap2 normalizationF p (normalizationData A D w)
  let m := model p A D w
  have hA := le_trans hD hDA
  have hs : Γ ⊢[PRAAx] GaussianStirlingNames.source A D := .andI hA hD
  have hU := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hA hU
  have flip := cross_symm SF logGammaF yd gd (logarithmic_cancellation A D w hs)
  have first : Γ ⊢[PRAAx] distanceBounded g y two U :=
    diagonal_at logGammaF SF gd yd p (cross_to_diagonal logGammaF SF gd yd flip)
  have second := add_sample_error remainderF normalizationF (remainderData A D w) (normalizationData A D w) p
    (remainder_regular A D w hs) (normalization_regular A D w hs)
  have third := sum_distance r r t m _ _ _ hU (distance_refl_zero r _ hU) (normalization_error p A D w hs)
  have approx : Γ ⊢[PRAAx] distanceBounded g (qadd r m) (num 16+two*A) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
      (distance_triangle_same g y (qadd r m) _ _ U hU first
        (distance_triangle_same y (qadd r t) (qadd r m) _ _ U hU second third))
  have scaled : Γ ⊢[PRAAx] distanceBounded g (qadd r m) ((num 16+two*A)*A) (A*U) :=
    distance_radius_mono _ _ _ _ _ _ hU hd (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) approx
  have near := (GaussianReconstructionRoots.distance_zero_iff r _ _ hd).iffMpr (remainder_bound p A D w hs hDA)
  have tail : Γ ⊢[PRAAx] distanceBounded (qadd r m) m (two*D*U+two*A) (A*U) :=
    distance_congr (.eqRefl _) (qzero_add m (qadd_canonical _ _)) (by ipra_ring) (.eqRefl _)
      (sum_distance r qzero m m _ _ _ hd near (distance_refl_zero m _ hd))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same g (qadd r m) m _ _ _ hd scaled tail)

end LeanProofs.IPRA.Analysis.GaussianRaabeStirlingRemainder
