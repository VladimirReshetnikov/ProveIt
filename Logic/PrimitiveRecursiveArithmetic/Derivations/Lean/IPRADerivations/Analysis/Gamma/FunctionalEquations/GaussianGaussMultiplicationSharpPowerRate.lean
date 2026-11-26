import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationLimitMajorant
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationPowerPerturbation

/-!
# Sharp Gauss multiplication power comparison

The two actual exponential names satisfy the bound
(2m(R+1)m^{m(R+1)}/N) with the dyadic error of each observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationSharpPowerRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGaussMultiplicationPowerRate (amplification powerF)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (R m : PTm n) : PTm n := two*amplification R m*GaussianGaussMultiplicationLimitMajorant.height R m

@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (coefficient R m) = coefficient (Syn.subst σ R) (Syn.subst σ m) := by simp [coefficient]

theorem sharp_rate (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N)
    (hA : Γ ⊢[PRAAx] le (amplification R m) N) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    independentRate powerF powerF (rowData z R B m N)
      (GaussianGaussMultiplicationPowerPerturbation.limitData z R B m) (coefficient R m) N := by
  open GaussianGaussMultiplicationLimitMajorant in
  have bound : Γ ⊢[PRAAx] sampleBound limitF (limitData z R B m) (height R m) := by
    refine .allI ?_
    let sh (u : PTm n) := Syn.shift u
    have ms : Γ.map Fm.shift ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
    have bs : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh] using hB.shift
    have zs : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) := by
      simpa [Fm.shift,Syn.shift,sh] using hz.shift
    simpa [sampleBound,Syn.shift,sh] using limit_bound_at (sh z) (sh R) (sh B) (sh m) (var 0) ms bs zs
  open GaussianGaussMultiplicationLimitMajorant in
  exact GaussianGaussMultiplicationPowerPerturbation.weighted_power_rate_via limitF (limitData z R B m) z R B m N
    (height R m) hm hN hA hB hz (GaussianRadiusExponentialName.name_regular _ _ _ (alternative_input z R B m hm hB hz))
    (limit_cross z R B m hm hB hz) bound

theorem actual_gauss_multiplication_sharp_power_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ (le one (var 4) ⋏ (le (amplification (var 1) (var 3)) (var 4) ⋏
      (le one (var 2) ⋏ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2))))) ⟶
        independentRate powerF powerF (rowData (var 0) (var 1) (var 2) (var 3) (var 4))
          (GaussianGaussMultiplicationPowerPerturbation.limitData (var 0) (var 1) (var 2) (var 3))
          (coefficient (var 1) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (sharp_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationSharpPowerRate
