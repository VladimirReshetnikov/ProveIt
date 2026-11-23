import IPRADerivations.Analysis.GaussianEulerIntegerMomentUniform

/-!
# Original Euler powers at an exact internal natural coefficient

An exact finite equality of the original Euler coefficient with the
natural point N identifies its ORIGINAL power data with the existing
exp(N log t) sampler. The checked integer-exponential theorem then
returns the literal normalized rational monomial t^N. No equation for
the exponential output is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNaturalPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (coefficient powerF powerData powerExponentF logarithmF)
open GaussianGammaCanonicalExponent (constantF)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientData (k a b : PTm n) : PTm n := GaussianGammaFiniteApproximantName.exponentialInputData powerExponentF
  (GaussianNameArithmetic.multiplyData constantF logarithmF k (GaussianPositiveRationalLogarithm.data a b))
@[simp] theorem subst_coefficientData {m : ℕ} (σ : Fin n → PTm m) (k a b : PTm n) :
    Syn.subst σ (coefficientData k a b) = coefficientData (Syn.subst σ k) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [coefficientData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem original_data (z B N a b : PTm n) (hc : Γ ⊢[PRAAx] coefficient z B ≐ naturalPoint N) : Γ ⊢[PRAAx]
    powerData z B a b ≐ GaussianHarmonicIntegerExponential.originalData N a b := by
  change Γ ⊢[PRAAx] coefficientData (coefficient z B) a b ≐ coefficientData (naturalPoint N) a b
  simpa only [subst_coefficientData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (coefficientData (var 0) (Syn.shift a) (Syn.shift b)) hc

theorem original_power (z B N a b E T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b E T)
    (hc : Γ ⊢[PRAAx] coefficient z B ≐ naturalPoint N) : Γ ⊢[PRAAx]
    crossEquivalent powerF constantF (powerData z B a b) (GaussianEulerIntegerMomentIntegrand.monomial N a b) := by
  have left := GaussianEulerIntegrandName.power_regular z B a b (.andI hB ht.andE₂.andE₁)
  have right : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN powerF (GaussianHarmonicIntegerExponential.originalData N a b) :=
    GaussianRadiusExponentialName.name_regular _ _ _ (GaussianGammaFiniteApproximantName.exponential_input _ _
      (GaussianHarmonicIntegerExponential.original_exponent_regular N a b E T ht))
  have move := GaussianGammaInputProperness.code_data_cross powerF _ _ left right (original_data z B N a b hc)
  exact cross_trans _ _ _ _ _ _ move (cross_trans _ _ _ _ _ _
    (GaussianHarmonicIntegerExponential.original_integer_exponential N a b E T ht)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianHarmonicIntegerExponential.actual_rational_power a b N ht.andE₂.andE₁.andE₂).eqSymm))

theorem actual_original_Euler_natural_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 1) ⟶ GaussianHarmonicIntegerExponential.source (var 3) (var 4) (var 5) (var 6) ⟶
      coefficient (var 0) (var 1) ≐ naturalPoint (var 2) ⟶ crossEquivalent powerF constantF
        (powerData (var 0) (var 1) (var 3) (var 4)) (GaussianEulerIntegerMomentIntegrand.monomial (var 2) (var 3) (var 4))) :=
  closeUniv 7 (.impI (.impI (.impI (original_power _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerNaturalPower
