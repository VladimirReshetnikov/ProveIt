import IPRADerivations.Analysis.GaussianBohrMollerupPresentation
import IPRADerivations.Analysis.GaussianStirlingLogDuplication
import IPRADerivations.Analysis.GaussianGammaInputProperness
import IPRADerivations.Analysis.GaussianRobinMeshExponential
import IPRADerivations.Analysis.GaussianExponentialInverse
import IPRADerivations.Analysis.GaussianGammaRationalWendelGautschi

/-!
# Original positive rational log Gamma is normalized at one

The native arguments are identified by Gaussian value, then the original
Gamma normalization and injectivity of the real exponential identify
the actual logarithm with the zero name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupNativeNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianBohrMollerupPresentation (native normalization laws)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (cross_trans cross_symm)
open GaussianNameRingLaws (zeroF)
open GaussianStirlingGammaLogarithm (source arg logGammaF logGammaData log_gamma_axis log_gamma_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem native_normalization : Γ ⊢[PRAAx] normalization native := by
  let a : PTm n := one
  let x := logGammaData a a
  let R := U logGammaF x
  have hs : Γ ⊢[PRAAx] source a a := .andI (le_refl _) (le_refl _)
  have hh := log_gamma_regular a a hs
  have equal_arguments : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (arg a) (oneCode : PTm n) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [arg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,a,one] <;>
      try (ipra_simps; ring)
  have changeArg := GaussianGammaInputProperness.original_Gamma_proper (arg a) oneCode a a a a
    (GaussianStirlingGammaLogarithm.gamma_source a a hs) equal_arguments
  have original := GaussianStirlingLogDuplication.exponential_gamma a a hs
  have e0 := GaussianExponentialInverse.zero_exponential_cross (Γ := Γ) one zero
  have equalExp := cross_trans _ _ _ _ _ _ original
    (cross_trans _ _ _ _ _ _ changeArg
      (cross_trans _ _ _ _ _ _ GaussianRobinMeshExponential.C21_Gamma_one
        (cross_symm _ _ _ _ e0)))
  have axis0 : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples zeroF zero := by
    refine .allI ?_
    exact RationalGaussianEmbedding.axis_congr
      (GaussianNameRingLaws.zero_at (var 0) _).eqSymm RationalGaussianEmbedding.axis_zero
  have res := GaussianRealNameExponentialInjectivity.independent_radii_injective logGammaF zeroF R one x zero
    (exponential_input _ _ hh) (GaussianExponentialInverse.zero_input _ _)
    (log_gamma_axis a a) axis0 equalExp
  simpa only [normalization,GaussianBohrMollerupPresentation.native_program,
    GaussianBohrMollerupPresentation.native_argument,a,x] using res

theorem native_laws : Γ ⊢[PRAAx] laws native :=
  .andI native_normalization (.andI GaussianBohrMollerupPresentation.native_values
    (.andI GaussianBohrMollerupPresentation.native_recurrence
      (.andI GaussianBohrMollerupPresentation.native_rescaling GaussianBohrMollerupPresentation.native_convexity)))

theorem actual_native_log_gamma_Bohr_Mollerup_laws_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] laws native :=
  native_laws

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupNativeNormalization
