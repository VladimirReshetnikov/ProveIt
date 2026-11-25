import IPRADerivations.Analysis.GaussianNamedPositiveDigamma
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedTerminalProperness

/-!
# Properness of the original positive digamma and derivative names

The argument names may have different observation programs and independent
positive margins. Exact properness of the Euler and reciprocal programs
transfers to the normalized digamma.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveDigammaProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (original_euler_proper original_gamma_proper)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal)
open GaussianNamedGammaFirstCrossing (inverseClock)
open GaussianNamedPositiveDigamma (source nameF data derivativeF derivativeData derivative_regular
  inverseF inverseData inverse_input inverse_regular)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem derivative_proper (f g : PR 2) (x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A) (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (derivativeF f) (derivativeF g) (derivativeData x A) (derivativeData y B) :=
  original_euler_proper f g one x y A B hf.andE₁ hg.andE₁ he

theorem inverse_proper (f g : PR 2) (x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A) (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (inverseF f) (inverseF g) (inverseData x A) (inverseData y B) := by
  have a := inverse_input f x A hf
  have b := inverse_input g y B hg
  exact GaussianNameReciprocal.names_equivalent (GaussianNamedGamma.nameF f) (GaussianNamedGamma.nameF g)
    inverseClock inverseClock (GaussianNamedGamma.data x A) (GaussianNamedGamma.data y B)
    a.andE₁ b.andE₁ a.andE₂ b.andE₂
    (cross_to_diagonal _ _ _ _ (original_gamma_proper f g x y A B hf.andE₁ hg.andE₁ he))

theorem proper (f g : PR 2) (x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A) (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x A) (data g y B) :=
  multiply_cross (inverseF f) (inverseF g) (derivativeF f) (derivativeF g)
    (inverseData x A) (inverseData y B) (derivativeData x A) (derivativeData y B)
    (inverse_regular f x A hf) (inverse_regular g y B hg)
    (derivative_regular f x A hf) (derivative_regular g y B hg)
    (inverse_proper f g x y A B hf hg he) (derivative_proper f g x y A B hf hg he)

theorem actual_original_named_positive_digamma_proper_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ (source g (var 1) (var 3) ⋏ crossEquivalent f g (var 0) (var 1))) ⟶
        crossEquivalent (nameF f) (nameF g) (data f (var 0) (var 2)) (data g (var 1) (var 3))) :=
  closeUniv 4 (.impI (proper f g _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveDigammaProperness
