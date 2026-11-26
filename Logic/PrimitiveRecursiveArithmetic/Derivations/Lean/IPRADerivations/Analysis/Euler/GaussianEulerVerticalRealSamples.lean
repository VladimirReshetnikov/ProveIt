import IPRADerivations.Analysis.Euler.GaussianEulerVerticalNativeProjection
import IPRADerivations.Analysis.Euler.GaussianEulerRealIntegrandNonnegative

/-!
# Actual real observations of the original real-argument Euler integrand

Every exponential of an actually real exponent observation is fixed by
conjugation at its original series clock. The unchanged original Euler
program at native(Re z)/B therefore has canonical real observations and
its original nonnegative lower envelope, at arbitrary positive times.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalRealSamples

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianRationalConjugation (point point_congr)
open GaussianEulerVerticalNativeProjection (argument imaginary_zero)
open GaussianRadiusExponentialName (inputPrecision index nameF data)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem real_input_fixed (f : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    point (ap2 f p x) ≐ ap2 f p x := by
  have real := real_sample_at f x p h
  have same := RationalGaussianEmbedding.canonical_axis_roundtrip _ real.andE₁ real.andE₂
  exact (point_congr same.eqSymm).eqTrans ((GaussianRationalConjugation.point_embed _).eqTrans same)

theorem original_exponential_fixed (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    point (ap2 (nameF f) p (data R x)) ≐ ap2 (nameF f) p (data R x) := by
  have sample := GaussianRadiusExponentialName.sample_at (Γ := Γ) f R p x
  exact (point_congr sample).eqTrans ((GaussianRationalConjugation.point_scalar_sum _ _).eqTrans
    ((GaussianNameConjugation.scalar_sum_congr (index R p) (real_input_fixed f (inputPrecision R p) x h)).eqTrans sample.eqSymm))

theorem original_exponential_real_at (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF f) p (data R x)) ⋏ RationalGaussianEmbedding.axis (ap2 (nameF f) p (data R x)) :=
  .andI (GaussianRadiusExponentialName.sample_canonical f R p x)
    (RationalGaussianEmbedding.axis_congr
      (GaussianEulerDecayRealSamples.fixed_axis_embedding _ (original_exponential_fixed f R x p h))
      (RationalGaussianEmbedding.embed_axis _))

theorem original_exponential_real_samples (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    realSamples (nameF f) (data R x) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [realSamples,GaussianRadiusExponentialName.subst_data,Syn.shift] using
    original_exponential_real_at f (Syn.shift R) (Syn.shift x) (var 0) hs

theorem real_argument_input (z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    GaussianEulerRealIntegrandNonnegative.source (argument z) B a b := .andI hB (.andI (imaginary_zero z) ht)

theorem original_real_integrand_samples (z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    realSamples GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data (argument z) B a b) :=
  original_exponential_real_samples GaussianEulerIntegrandName.exponentF _ _
    (GaussianEulerRealIntegrandNonnegative.exponent_real_samples _ _ _ _ (real_argument_input z B a b hB ht))

theorem original_real_integrand_nonnegative (p z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper RationalGaussianEmbedding.scalarZero
      (fstT (ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data (argument z) B a b)))
      one (GaussianCoefficientNameBounds.unit p) :=
  GaussianEulerRealIntegrandNonnegative.original_name_nonnegative _ _ _ _ _ (real_argument_input z B a b hB ht)

theorem original_vertical_real_Euler_samples_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ GaussianPositiveRationalLogarithm.source (var 2) (var 3)) ⟶
      realSamples GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data (argument (var 0)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_real_integrand_samples _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalRealSamples
