import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherFinite
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRationalTelescopers

/-!
# Exact rational coefficients of the leading Barnes asymptotic

The retained Stirling correction scales to `1/12`. The logarithmic
factor and the quadratic contribution simplify at their actual encoded
rational arguments before taking any asymptotic comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerLeadingCoefficients

open_ipra
open ComplexLogarithmRemainder (code scale oneCode eval_re_code eval_im_code)
open GaussianBarnesGlaisherQuartic (negativeWeight weightNumerator)
open GaussianBarnesGlaisherFinite (squareQuarter)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical qadd qmul
  qadd_represents qmul_represents canonical_unique qadd_canonical qmul_canonical represents
  represents_rescale represents_congr positive_product)
open GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_add im_add re_scale im_scale
  re_sub im_sub re_neg im_neg re_mul im_mul re_one im_one)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianStirlingNames (offset)
open GaussianStirlingRationalTelescopers (upperValue)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "neg" => ComplexLogarithmRemainder.neg
local notation "gadd" => ComplexLogarithmRemainder.add
local notation "gmul" => ComplexLogarithmRemainder.mul
local notation "gsub" => GaussianRootAlgebra.sub

def logarithmicNumerator (N : PTm n) : PTm n := code ⟨num 6*N*N,one⟩ (ZT.ofNat zero)
def logarithmicCoefficient (N : PTm n) : PTm n := ofGaussian (logarithmicNumerator N) (num 12)
def quadraticTerm (N : PTm n) : PTm n := ofGaussian (neg (scale (num 3*N*N) oneCode)) (num 4)
def constantCorrection : PTm n := ofGaussian oneCode (num 12)

theorem shifted_offset_represents (N : PTm n) : Γ ⊢[PRAAx]
    represents (qadd qone (offset N one)) (scale (two*N+one) oneCode) two := by
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have hN : Γ ⊢[PRAAx] represents (naturalPoint N) (scale two (scale N oneCode)) two :=
    represents_congr (.eqRefl _) (equal_refl _) (one_mul two)
      (represents_rescale _ _ _ two (natural_point_represents N))
  have half : Γ ⊢[PRAAx] represents (GaussianStirlingNames.point one two) (scale one oneCode) two :=
    ofGaussian_represents _ _ h2
  have sub := qsub_represents _ _ _ _ _ h2 hN half
  have raw := qadd_represents _ _ _ _ _ h2 (qone_represents_scaled two) sub
  have native : Γ ⊢[PRAAx] equal
      (gadd (scale two oneCode) (gsub (scale two (scale N oneCode)) (scale one oneCode)))
      (scale (two*N+one) oneCode) := by
    apply equal_of_values <;>
      simp only [re_add,im_add,re_scale,im_scale,re_sub,im_sub,re_one,im_one] <;> ipra_simps <;> ring
  exact represents_congr (.eqRefl _) native (.eqRefl _) raw

theorem logarithmic_coefficient (N : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (naturalPoint N) (qadd qone (offset N one))) (negativeWeight N) ≐ logarithmicCoefficient N := by
  let D : PTm n := num 12
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have hd : Γ ⊢[PRAAx] le one D := zero_lt_succ (num 11)
  have prod := qmul_represents _ _ _ _ _ _ (le_refl one) h2 (natural_point_represents (Γ := Γ) N)
    (shifted_offset_represents N)
  have eD : Γ ⊢[PRAAx] (one*two)*num 6 ≐ D := by unfold D; ipra_ring
  have weighted := represents_congr (.eqRefl _) (equal_refl _) eD (represents_rescale _ _ _ (num 6) prod)
  have tail : Γ ⊢[PRAAx] represents (negativeWeight N) (neg (scale (weightNumerator N) oneCode)) D :=
    ofGaussian_represents _ _ hd
  have raw := qadd_represents _ _ _ _ _ hd weighted tail
  have native : Γ ⊢[PRAAx] equal
      (gadd (scale (num 6) (gmul (scale N oneCode) (scale (two*N+one) oneCode)))
        (neg (scale (weightNumerator N) oneCode))) (logarithmicNumerator N) := by
    apply equal_of_values
    · simp only [re_add,re_scale,re_mul,im_scale,re_neg,re_one,im_one,logarithmicNumerator,eval_re_code]
      change _ = Groth.ι (Q.mk Γ (num 6*N*N)) - Groth.ι (Q.mk Γ one)
      unfold weightNumerator
      ipra_simps
      ring
    · simp only [im_add,im_scale,im_mul,re_scale,im_neg,re_one,im_one,logarithmicNumerator,eval_im_code,
        ZT.toZ_ofNat,Q.mk_zero,map_zero]
      ring
  exact canonical_unique _ _ _ D (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) native (.eqRefl _) raw) (ofGaussian_represents _ _ hd)

theorem quadratic_coefficient (N : PTm n) : Γ ⊢[PRAAx]
    qsub (squareQuarter N) (qmul (naturalPoint N) (naturalPoint N)) ≐ quadraticTerm N := by
  let D : PTm n := num 4
  have hd : Γ ⊢[PRAAx] le one D := zero_lt_succ (num 3)
  have sq := qmul_represents _ _ _ _ _ _ (le_refl one) (le_refl one) (natural_point_represents (Γ := Γ) N)
    (natural_point_represents N)
  have eqD : Γ ⊢[PRAAx] (one*one)*D ≐ D := by ipra_ring
  have scaled := represents_congr (.eqRefl _) (equal_refl _) eqD (represents_rescale _ _ _ D sq)
  have base : Γ ⊢[PRAAx] represents (squareQuarter N) (scale (N*N) oneCode) D := ofGaussian_represents _ _ hd
  have raw := qsub_represents _ _ _ _ _ hd base scaled
  have native : Γ ⊢[PRAAx] equal
      (gsub (scale (N*N) oneCode) (scale D (gmul (scale N oneCode) (scale N oneCode))))
      (neg (scale (num 3*N*N) oneCode)) := by
    apply equal_of_values <;>
      simp only [re_sub,im_sub,re_scale,im_scale,re_mul,im_mul,re_neg,im_neg,re_one,im_one,D] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ D (qsub_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) native (.eqRefl _) raw) (ofGaussian_represents _ _ hd)

theorem first_stirling_correction (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qmul (naturalPoint N) (upperValue N one) ≐ constantCorrection := by
  let D : PTm n := num 12
  have h12 : Γ ⊢[PRAAx] le one D := zero_lt_succ (num 11)
  have hd := positive_product D N h12 hN
  have right : Γ ⊢[PRAAx] represents (upperValue N one) (scale one oneCode) (D*N) :=
    ofGaussian_represents _ _ hd
  have prod := qmul_represents _ _ _ _ _ _ (le_refl one) hd (natural_point_represents (Γ := Γ) N) right
  have raw := represents_congr (.eqRefl _) (equal_refl _) (one_mul _) prod
  have native : Γ ⊢[PRAAx] equal (gmul (scale N oneCode) (scale one oneCode)) (scale N oneCode) := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ (D*N) (qmul_canonical _ _) (ofGaussian_canonical _ _ h12) hd
    (represents_congr (.eqRefl _) native (.eqRefl _) raw)
    (represents_rescale _ _ _ N (ofGaussian_represents _ _ h12))

theorem actual_Barnes_leading_asymptotic_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let N := var 0
     le one N ⟶
       (qadd (qmul (naturalPoint N) (qadd qone (offset N one))) (negativeWeight N) ≐ logarithmicCoefficient N) ⋏
       ((qsub (squareQuarter N) (qmul (naturalPoint N) (naturalPoint N)) ≐ quadraticTerm N) ⋏
         (qmul (naturalPoint N) (upperValue N one) ≐ constantCorrection))) :=
  closeUniv 1 (.impI (.andI (logarithmic_coefficient _) (.andI (quadratic_coefficient _)
    (first_stirling_correction _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerLeadingCoefficients
