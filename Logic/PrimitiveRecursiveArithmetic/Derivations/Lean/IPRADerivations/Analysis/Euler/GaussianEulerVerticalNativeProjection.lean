import IPRADerivations.Analysis.Gamma.GaussianGammaRealValues
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerPowerCoefficients
import IPRADerivations.Core.CertificateTactics

/-!
# Original native real arguments for the vertical Euler comparison

Project only the actual signed native numerator and keep its original
positive denominator. The input disk and positive real margin are
preserved exactly. The unchanged original Euler coefficient at that real
argument is the canonical real projection of the original coefficient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNativeProjection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (native)
open GaussianGammaRealValues (projection projection_represents)
open GaussianEulerIntegrandName (coefficient coefficient_represents)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique represents_congr)
open GaussianEulerLowerPowerCoefficients (realLower source)
open ComplexLogarithmRemainder (re im normSq scale oneCode)
open GaussianRootAlgebra (sub equal equal_of_values)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (z : PTm n) : PTm n := native (re z)
@[simp] theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (argument z) = argument (Syn.subst σ z) := by simp [argument]

theorem real_coordinate (z : PTm n) : Γ ⊢[PRAAx] ZT.eq (re (argument z)) (re z) := by
  apply ZT.derive
  simp only [argument,native,ComplexLogarithmRemainder.eval_re_code]
theorem imaginary_zero (z : PTm n) : Γ ⊢[PRAAx] ZT.eq (im (argument z)) (ZT.ofNat zero) := by
  apply ZT.derive
  simp only [argument,native,ComplexLogarithmRemainder.eval_im_code]

theorem norm_contraction (z : PTm n) : Γ ⊢[PRAAx] le (normSq (argument z)) (normSq z) := by
  apply le_of_eq_add (d := normSq (ComplexLogarithmRemainder.code (ZT.ofNat zero) (im z)))
  ipra_lc [ComplexLogarithmRemainder.normSq_eval, argument, native, ComplexLogarithmRemainder.eval_re_code, ComplexLogarithmRemainder.eval_im_code]

theorem upper_source (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) : Γ ⊢[PRAAx]
    GaussianEulerUpperPowerCoefficients.source (argument z) R B :=
  .andI h.andE₁ (le_trans (norm_contraction z) h.andE₂)

theorem real_margin (z A B : PTm n) (h : Γ ⊢[PRAAx] realLower z A B) : Γ ⊢[PRAAx] realLower (argument z) A B :=
  PolynomialBisection.zle_congr rfl (by
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,argument,native,ComplexLogarithmRemainder.eval_re_code]) h

theorem lower_source (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] source (argument z) R B A :=
  .andI h.andE₁ (.andI (upper_source z R B h.andE₂.andE₁) (real_margin z A B h.andE₂.andE₂))

theorem original_fraction_projection (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    ofGaussian (argument z) B ≐ projection (ofGaussian z B) :=
  canonical_unique _ _ (argument z) B (ofGaussian_canonical _ _ hB) (RationalGaussianEmbedding.embed_canonical _) hB
    (ofGaussian_represents _ _ hB) (projection_represents _ _ _ (ofGaussian_represents _ _ hB))

theorem coefficient_native_value (z B : PTm n) : Γ ⊢[PRAAx]
    equal (native (re (sub z (scale B oneCode)))) (sub (argument z) (scale B oneCode)) := by
  apply equal_of_values
  all_goals simp only [argument,native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
  all_goals ipra_simps
  all_goals ring

theorem original_coefficient_projection (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    projection (coefficient z B) ≐ coefficient (argument z) B :=
  canonical_unique _ _ (sub (argument z) (scale B oneCode)) B (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalMetric.qsub_canonical _ _) hB
    (represents_congr (.eqRefl _) (coefficient_native_value z B) (.eqRefl _)
      (projection_represents _ _ _ (coefficient_represents z B hB)))
    (coefficient_represents (argument z) B hB)

theorem actual_vertical_native_real_argument_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      (source (argument (var 0)) (var 1) (var 2) (var 3) ⋏
        (ZT.eq (im (argument (var 0))) (ZT.ofNat zero) ⋏
          (projection (coefficient (var 0) (var 2)) ≐ coefficient (argument (var 0)) (var 2))))) :=
  closeUniv 4 (.impI (.andI (lower_source _ _ _ _ Prf.hyp0)
    (.andI (imaginary_zero _) (original_coefficient_projection _ _ Prf.hyp0.andE₂.andE₁.andE₁))))
theorem actual_original_fraction_real_projection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ (ofGaussian (argument (var 0)) (var 1) ≐ projection (ofGaussian (var 0) (var 1)))) :=
  closeUniv 2 (.impI (original_fraction_projection _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNativeProjection
