import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicative
import IPRADerivations.Analysis.Stirling.Wallis.GaussianStirlingWallisGammaRatio
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingGammaLogShift

/-!
# The original factorial normalization of the Stirling quotient

At an integer argument, the native Gamma shift moves an exact integer
factor to the numerator. The native factorial identity then identifies
that numerator, and the same integer factor is included in the
normalization.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsQuotient

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFactorialValues (factorialValue)
open GaussianGammaReciprocalInverse (gammaF constant_inverse inverse_pairs named_product_exchange)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left negative_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingLogDuplication (exponential_regular)
open GaussianStirlingMultiplicative (quotientF quotientData expRemainderF expRemainderData reciprocalF reciprocalData
  denominatorF denominatorData sqrtF sqrtData sqrt_regular powerF powerData decayF decayData factor_inverse multiplicative_formula)
open GaussianStirlingMultiplicativeAlgebra (normalizationF normalizationData normalization_regular)
open GaussianStirlingNames (source gammaData gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev factorialDenominatorF : PR 2 := multiplyF constantF denominatorF
def factorialDenominatorData (i x : PTm n) : PTm n :=
  multiplyData constantF denominatorF (fraction i one) (denominatorData i one x)
abbrev factorialReciprocalF : PR 2 := multiplyF constantF reciprocalF
def factorialReciprocalData (i x : PTm n) : PTm n :=
  multiplyData constantF reciprocalF (fraction one i) (reciprocalData i one x)
abbrev factorialRatioF : PR 2 := multiplyF constantF factorialReciprocalF
def factorialRatioData (i x : PTm n) : PTm n :=
  multiplyData constantF factorialReciprocalF (factorialValue i) (factorialReciprocalData i x)

private theorem gamma_successor_data (i : PTm n) :
    Γ ⊢[PRAAx] gammaData (i+one) one ≐ gammaData (ConciseIPRA.PTm.succ i) one := by
  simpa only [GaussianStirlingGammaLogarithm.subst_gammaData,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (gammaData (var 0) (var 1) : PTm 2)
      (σ := ![i+one,one]) (σ' := ![ConciseIPRA.PTm.succ i,one])
      (fun j => by fin_cases j; exact (succ_eq_add_one i).eqSymm; exact .eqRefl _)

theorem integer_gamma_scaled (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF gammaF) constantF
      (multiplyData constantF gammaF (fraction i one) (gammaData i one)) (factorialValue i) := by
  have h : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have shift := GaussianStirlingGammaLogShift.gamma_increment i one h
  have move := GaussianGammaRealValues.cross_right_data (gamma_successor_data i) (cross_symm _ _ _ _ shift)
  exact cross_trans _ _ _ _ _ _ move (GaussianStirlingWallisGammaRatio.integer_factorial_cross i)

private theorem scalar_inverse (i y : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) oneF
      (multiplyData constantF constantF (fraction i one) (fraction one i)) y := by
  apply constant_inverse
  have c : Γ ⊢[PRAAx] fraction one one ≐ GaussianRationalSyntheticDivision.qone :=
    GaussianRationalHorner.canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
      GaussianRationalSyntheticDivision.qone_canonical (le_refl one)
      (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
      (GaussianRationalReciprocal.qone_represents_scaled one)
  exact (GaussianEulerDampedTimeRate.fraction_product i one one i (le_refl one) hi).eqTrans
    ((GaussianStirlingRationalTelescopers.fraction_same (i*one) (one*i) one one
      (le_congr (.eqRefl _) (one_mul i).eqSymm hi) (le_refl one) (by ipra_ring)).eqTrans c)

private theorem inverse_regular (i x : PTm n) (hs : Γ ⊢[PRAAx] source i one) :
    Γ ⊢[PRAAx] pointCN reciprocalF (reciprocalData i one x) :=
  exponential_regular _ _ (negative_fast normalizationF (normalizationData i one x) (normalization_regular i one x hs))

theorem factorial_ratio_regular (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] pointCN factorialRatioF (factorialRatioData i x) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (multiply_fast _ _ _ _ (constant_regular _) (inverse_regular i x (.andI hi (le_refl one))))

theorem factorial_denominator_inverse (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF factorialDenominatorF factorialReciprocalF) oneF
      (multiplyData factorialDenominatorF factorialReciprocalF
        (factorialDenominatorData i x) (factorialReciprocalData i x)) (normalizationData i one x) := by
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have power := GaussianStirlingNames.product_regular i one hs
  have decay := exponential_regular _ _ (negative_fast constantF (fraction i one) (constant_regular (Γ := Γ) _))
  have hr : Γ ⊢[PRAAx] pointCN denominatorF (denominatorData i one x) :=
    multiply_fast _ _ _ _ (multiply_fast _ _ _ _ (sqrt_regular x) (exponential_regular _ _ power)) decay
  exact inverse_pairs constantF denominatorF constantF reciprocalF (fraction i one)
    (denominatorData i one x) (fraction one i) (reciprocalData i one x) (normalizationData i one x)
    (constant_regular _) hr (constant_regular _) (inverse_regular i x hs)
    (scalar_inverse i _ hi) (factor_inverse i one x hs)

set_option maxHeartbeats 700000 in
theorem factorial_ratio (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent quotientF factorialRatioF (quotientData i one x) (factorialRatioData i x) := by
  let M := multiplyF constantF gammaF
  let N := multiplyF constantF constantF
  let a := fraction i one
  let b := gammaData i one
  let c := fraction one i
  let d := reciprocalData i one x
  let q := quotientData i one x
  let f := factorialReciprocalData i x
  let w := multiplyData constantF gammaF a b
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have ha := constant_regular (Γ := Γ) a
  have hb := gamma_regular i one hs
  have hc := constant_regular (Γ := Γ) c
  have hd := inverse_regular i x hs
  have hq : Γ ⊢[PRAAx] pointCN quotientF q := multiply_fast _ _ _ _ hb hd
  have hf : Γ ⊢[PRAAx] pointCN factorialReciprocalF f := multiply_fast _ _ _ _ hc hd
  have reduction := multiply_cross N oneF quotientF quotientF (multiplyData constantF constantF a c) q q q
    (multiply_fast _ _ _ _ ha hc) (one_fast q) hq hq (scalar_inverse i q hi) (cross_refl _ _ hq)
  have exchange := named_product_exchange constantF gammaF constantF reciprocalF a b c d ha hb hc hd
  have renamed := multiply_cross M constantF factorialReciprocalF factorialReciprocalF w (factorialValue i) f f
    (multiply_fast _ _ _ _ ha hb) (constant_regular _) hf hf (integer_gamma_scaled i hi) (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_one_left quotientF q hq))
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ reduction) (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ exchange) renamed))

theorem exp_remainder_is_factorial_ratio (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent expRemainderF factorialRatioF (expRemainderData i one x) (factorialRatioData i x) :=
  cross_trans _ _ _ _ _ _ (multiplicative_formula i one x (.andI hi (le_refl one))) (factorial_ratio i x hi)

theorem actual_factorial_Stirling_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ crossEquivalent expRemainderF factorialRatioF
      (expRemainderData (var 0) one (var 1)) (factorialRatioData (var 0) (var 1))) :=
  closeUniv 2 (.impI (exp_remainder_is_factorial_ratio _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsQuotient
