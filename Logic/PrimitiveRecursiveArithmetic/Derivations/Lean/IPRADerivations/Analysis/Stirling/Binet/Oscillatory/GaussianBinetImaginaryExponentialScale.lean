import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatoryPanelFactor

/-!
# Rational rescaling and reversal of actual imaginary exponents

The normalized Gaussian codes for the two imaginary signs scale by a
nonnegative rational exactly. This permits the two orders of variables
on the original cosine rectangle to use the same pointwise exponential.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetImaginaryExponentialScale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code oneCode scale)
open GaussianBinetExponentialIntegralGrid (exponent)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product canonical_unique qmul_canonical qmul_represents ofGaussian_represents represents_congr)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_neg im_neg re_scale im_scale re_one im_one)
open RationalArithmetic (select select_zero select_one)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem real_value (A : PTm n) (s : Bool) :
    ZT.toZ Γ (ComplexLogarithmRemainder.re (native zero A (polarity s))) = 0 := by
  simp [native,eval_re_code,ZT.toZ_ofNat]

private theorem imaginary_value (A : PTm n) (s : Bool) :
    ZT.toZ Γ (ComplexLogarithmRemainder.im (native zero A (polarity s))) = if s then -𝔞 A else 𝔞 A := by
  rw [native,eval_im_code]
  cases s
  · change 𝔞(select zero A zero) - 𝔞(select zero zero A) = 𝔞 A
    rw [natEq (select_zero (Γ := Γ) zero A zero (.eqRefl _)),natEq (select_zero (Γ := Γ) zero zero A (.eqRefl _))]
    ipra_simps
    ring
  · change 𝔞(select one A zero) - 𝔞(select one zero A) = -𝔞 A
    rw [natEq (select_one (Γ := Γ) one A zero (.eqRefl _)),natEq (select_one (Γ := Γ) one zero A (.eqRefl _))]
    ipra_simps
    ring

private theorem negative_rep (A B : PTm n) (s : Bool) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRationalHorner.represents (coefficient A B (polarity s))
      (ComplexLogarithmRemainder.neg (native zero A (polarity s))) B :=
  qnegative_represents (argument zero A B (polarity s)) _ _ (ofGaussian_represents _ _ hB)

theorem opposite (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qnegative (coefficient A B (polarity true)) ≐ coefficient A B (polarity false) := by
  apply canonical_unique _ _ _ B (qnegative_canonical _) (qnegative_canonical _) hB (hrv := negative_rep A B false hB)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := qnegative_represents _ _ _ (negative_rep A B true hB))
  apply equal_of_values
  · simp only [re_neg,real_value]
    ring
  · simp only [im_neg,imaginary_value,Bool.false_eq_true,ite_false,ite_true]
    ring

theorem exponent_scale (s : Bool) (A B a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    exponent (coefficient A B (polarity s)) a b ≐ coefficient (A*a) (B*b) (polarity s) := by
  let u := ComplexLogarithmRemainder.neg (native zero A (polarity s))
  let v := scale a oneCode
  have h := positive_product _ _ hB hb
  have q := qmul_represents _ (fraction a b) u v B b hB hb (negative_rep A B s hB) (ofGaussian_represents v b hb)
  apply canonical_unique _ _ _ (B*b) (qmul_canonical _ _) (qnegative_canonical _) h
    (hrv := negative_rep (A*a) (B*b) s h)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := q)
  dsimp only [u,v]
  apply equal_of_values
  · simp [re_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,real_value]
  · cases s <;> simp [im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,real_value,imaginary_value,Q.mk_mul,map_mul]

theorem coefficient_congr (s : Bool) {A A' B B' : PTm n}
    (ha : Γ ⊢[PRAAx] A ≐ A') (hb : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    coefficient A B (polarity s) ≐ coefficient A' B' (polarity s) := by
  have old (u : PTm 2) := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (coefficient (var 0) (var 1) u : PTm 2)
    (σ := ![A,B]) (σ' := ![A',B']) (fun j => by fin_cases j; exact ha; exact hb)
  cases s
  · simpa [polarity] using old zero
  · simpa [polarity] using old one

end LeanProofs.IPRA.Analysis.GaussianBinetImaginaryExponentialScale
