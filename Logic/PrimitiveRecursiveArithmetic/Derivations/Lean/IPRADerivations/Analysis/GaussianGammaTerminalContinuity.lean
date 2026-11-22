import IPRADerivations.Analysis.GaussianGammaPoleInverseContinuity
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# The fixed terminal reciprocal near a Gamma pole

The terminal argument of the local pole formula is the original
shift trajectory at 1+h/B. On the half disk it has the same
uniform pole certificate (1,2), including at h=0. Its actual
Gamma name inherits the reciprocal name's rate of approach to
one, with a fixed computed amplification.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaTerminalContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaLocalPoleGuards (terminal terminal_native terminal_Gamma_domain)
open GaussianGammaPoleInverseContinuity (halfDisk)
open GaussianGammaReciprocalInverse
  (gammaF gammaData inverseF inverseData lambdaNumerator lambdaDenominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr qone_bounded)
open GaussianRationalSyntheticDivision (qone)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open ComplexLogarithmRemainder (scale oneCode normSq normSq_scale)
open GaussianRootAlgebra (equal equal_of_values normSq_equal)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem two_positive : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one

def encodedOne (B : PTm n) : PTm n := scale B oneCode
def inverseBound : PTm n := lambdaDenominator two two

theorem uniform_terminal_domain (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] halfDisk h B) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (terminal h B j) two B one two :=
  terminal_Gamma_domain h B one one two j hB (le_refl one) two_positive
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl two))
    (le_congr (.eqRefl _) (by ipra_ring) hh)

theorem terminal_difference (h B j : PTm n) : Γ ⊢[PRAAx]
    equal (GaussianRootAlgebra.sub (terminal h B j) (encodedOne B)) h := by
  have t := terminal_native (Γ := Γ) h B j
  have tr := GaussianRootAlgebra.equal_re t
  have ti := GaussianRootAlgebra.equal_im t
  apply equal_of_values
  · simp only [GaussianRootAlgebra.re_sub, tr, GaussianGammaEulerHeadLower.translated, encodedOne,
      GaussianRootAlgebra.re_add, GaussianRootAlgebra.re_scale, GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  · simp only [GaussianRootAlgebra.im_sub, ti, GaussianGammaEulerHeadLower.translated, encodedOne,
      GaussianRootAlgebra.im_add, GaussianRootAlgebra.im_scale, GaussianRootAlgebra.im_one]
    ring

theorem terminal_input_distance (h B j C E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (scale E h) (C*B)) :
    Γ ⊢[PRAAx] distanceBounded (ofGaussian (terminal h B j) B) (ofGaussian (encodedOne B) B) C E := by
  apply (GaussianRationalMetric.bounded_difference_iff _ _ _ _ _ _ _ hB hE
    (ofGaussian_represents _ _ hB) (ofGaussian_represents _ _ hB)).iffMpr
  exact le_congr ((normSq_scale E h).eqTrans
    (congrMul (.eqRefl _) (normSq_equal (terminal_difference h B j)).eqSymm))
    (by ipra_ring) hh

private theorem exact_inverse_bound (z B : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z two B one two) :
    Γ ⊢[PRAAx] smallSamples inverseF (inverseData z two B) (inverseBound : PTm n) one := by
  refine .allI ?_
  have hs' : Γ.map Fm.shift ⊢[PRAAx]
      GaussianGammaReciprocalInverse.source (Syn.shift z) two (Syn.shift B) one two := by
    simpa [Fm.shift, Syn.shift, one, two] using hs.shift
  have b := bound_congr (.eqRefl _) (.eqRefl _)
    (GaussianPolynomialPerturbation.one_power _) (GaussianGammaReciprocalInverse.inverse_sample_bound
      (var 0) (Syn.shift z) two (Syn.shift B) one two hs')
  simpa [smallSamples, inverseBound, Syn.shift, one, two] using b

private theorem one_samples : Γ ⊢[PRAAx] smallSamples oneF (zero : PTm n) inverseBound one := by
  refine .allI ?_
  have hb := (GaussianGammaReciprocalInverse.lambda_positive two one two
    (le_refl one) (two_positive (Γ := Γ.map Fm.shift))).andE₂
  have b := GaussianCoefficientNameBounds.bounded_radius_mono qone one one
    (inverseBound : PTm (n+1)) one (le_refl one) (le_refl one)
    (mul_le_mul_right one hb) qone_bounded
  simpa [smallSamples, inverseBound, Syn.shift, one, two] using
    bound_congr (one_at (var 0) zero).eqSymm (.eqRefl _) (.eqRefl _) b

theorem terminal_gamma_rate (h B j C E : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] halfDisk h B) (hE : Γ ⊢[PRAAx] le one E)
    (hp : Γ ⊢[PRAAx] independentRate GaussianGammaC7Name.nameF oneF
      (GaussianGammaC7Name.data (terminal h B j) two B) zero C E) :
    Γ ⊢[PRAAx] independentRate gammaF oneF
      (gammaData (terminal h B j) two B two) zero (inverseBound*inverseBound*C) (one*one*E) := by
  let z := terminal h B j
  let x := GaussianGammaC7Name.data z two B
  let u := inverseData z two B
  let v := gammaData z two B two
  have hs := uniform_terminal_domain h B j hB hh
  have oneReg := one_fast (Γ := Γ) (zero : PTm n)
  have first := GaussianGammaC7Name.name_regular z two B hs.andE₁
  have inv := GaussianGammaReciprocalInverse.inverse_regular z two B hs.andE₁
  have inverseInput : Γ ⊢[PRAAx] GaussianNamedInverseRate.input GaussianGammaC7Name.nameF oneF inverseF oneF
      x zero u zero inverseBound one C E :=
    .andI (le_refl one) (.andI hE (.andI (.andI first oneReg) (.andI (.andI inv oneReg)
      (.andI (.andI (exact_inverse_bound z B hs) one_samples)
        (.andI (.andI (GaussianGammaReciprocalInverse.inverse_product z two B one two hs)
          (GaussianNameRingLaws.multiply_one oneF zero oneReg)) hp)))))
  have candidate := GaussianNamedInverseRate.inverse_rate GaussianGammaC7Name.nameF oneF inverseF oneF
    x zero u zero inverseBound one C E inverseInput
  have hden := positive_product _ _ (positive_product _ _ (le_refl one) (le_refl one)) hE
  have exchange : Γ ⊢[PRAAx] crossEquivalent gammaF inverseF v u :=
    (GaussianGammaReciprocalInverse.original_gamma_inverse z two B one two hs).andE₂
  exact GaussianNamedRateTransport.transport inverseF oneF gammaF oneF u zero v zero
    (inverseBound*inverseBound*C) (one*one*E) hden candidate exchange
    (cross_refl _ _ oneReg)

theorem original_terminal_input_metric_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 4) ⟶ ComplexLogarithmRemainder.bounded (scale (var 4) (var 0)) (var 3*var 1) ⟶
      distanceBounded (ofGaussian (terminal (var 0) (var 1) (var 2)) (var 1))
        (ofGaussian (encodedOne (var 1)) (var 1)) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (terminal_input_distance _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_terminal_inverse_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ halfDisk (var 0) (var 1) ⟶ le one (var 4) ⟶
      independentRate GaussianGammaC7Name.nameF oneF
        (GaussianGammaC7Name.data (terminal (var 0) (var 1) (var 2)) two (var 1)) zero (var 3) (var 4) ⟶
      independentRate gammaF oneF (gammaData (terminal (var 0) (var 1) (var 2)) two (var 1) two)
        zero (inverseBound*inverseBound*var 3) (one*one*var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (terminal_gamma_rate _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaTerminalContinuity
