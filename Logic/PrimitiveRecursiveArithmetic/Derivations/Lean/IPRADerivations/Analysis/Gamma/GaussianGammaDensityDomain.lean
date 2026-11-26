import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaRisingFactorial
import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Analysis.Gamma.GaussianGammaHalfPlaneInputContinuity

/-!
# Source-only domains for every internal Gamma-density moment

The native N-step trajectory adds BN to the real coordinate. The same
positive margin A therefore certifies every shifted parameter, and the
original disk grows only from R to R+N. Both original Gamma pole guards
and the V8 input are derived from this arithmetic source.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDensityDomain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianGammaShiftTrajectory (point)
open GaussianEulerLowerPowerCoefficients (realLower)
open ComplexLogarithmRemainder (re)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shifted_real_lower (z A B N : PTm n) (h : Γ ⊢[PRAAx] realLower z A B) : Γ ⊢[PRAAx]
    realLower (point z B N) A B := by
  have old := zle_toZ h
  have native := GaussianGammaShiftTrajectory.point_native (Γ := Γ) z B N
  apply zle_of_toZ (PolynomialBisection.slack (ZT.ofNat B) (ZT.ofNat A*re z)+A*B*N)
  simp only [PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_ofNat] at old ⊢
  rw [GaussianRootAlgebra.equal_re native]
  simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
  ipra_simps
  linear_combination old

theorem shifted_source (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    source (point z B N) (R+N) B A := by
  have original : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B :=
    .andI h.andE₂ h.andE₁.andE₂.andE₁
  have shifted := GaussianGammaShiftTrajectory.point_source z R B N original
  exact .andI (.andI h.andE₁.andE₁ (.andI (.andI h.andE₁.andE₂.andE₁.andE₁ shifted.andE₂.andE₂)
    (shifted_real_lower z A B N h.andE₁.andE₂.andE₂))) shifted.andE₁

theorem base_gamma_source (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source z R B one A :=
  GaussianGammaHalfPlaneInputContinuity.reciprocal_source z R B A h

theorem shifted_gamma_source (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (point z B N) (R+N) B one A :=
  GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ (shifted_source z R B A N h)

theorem rising_input (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianGammaRisingFactorial.input z R B one A one A N :=
  .andI (base_gamma_source z R B A h) (shifted_gamma_source z R B A N h).andE₂

theorem actual_original_Gamma_density_shifted_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      source (point (var 0) (var 2) (var 4)) (var 1+var 4) (var 2) (var 3)) :=
  closeUniv 5 (.impI (shifted_source _ _ _ _ _ Prf.hyp0))
theorem actual_original_Gamma_density_V8_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianGammaRisingFactorial.input (var 0) (var 1) (var 2) one (var 3) one (var 3) (var 4)) :=
  closeUniv 5 (.impI (rising_input _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDensityDomain
