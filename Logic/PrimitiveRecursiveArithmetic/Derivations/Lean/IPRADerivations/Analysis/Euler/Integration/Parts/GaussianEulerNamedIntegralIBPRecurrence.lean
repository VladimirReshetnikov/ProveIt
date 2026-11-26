import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerNamedIBPRecurrence
import IPRADerivations.Analysis.Euler.GaussianNamedEulerQuadrature

/-!
# Euler recurrence for the original named improper integrals

The shifted and unshifted improper quadratures agree with their own
Gamma programs. Product transport preserves the literal input name and
the normalized product observation. The resulting recurrence compares
independent observations of the actual improper Euler programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedIntegralIBPRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianNamedGamma (data)
open GaussianNamedEulerQuadrature (nameF name_regular original_named_Euler_integral_is_Gamma)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans cross_refl)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev productF (f : PR 2) : PR 2 := multiplyF f (nameF f)
def productData (f : PR 2) (x A : PTm n) : PTm n := multiplyData f (nameF f) x (data x A)

theorem original_named_Euler_IBP_recurrence (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (shiftF f)) (productF f) (data (shiftData x) A) (productData f x A) := by
  have left := original_named_Euler_integral_is_Gamma _ _ _ (GaussianEulerNamedShiftInput.original_source f x A h)
  have recurrence := GaussianEulerNamedIBPRecurrence.original_named_Gamma_IBP_recurrence f x A h
  have eq := original_named_Euler_integral_is_Gamma f x A h
  have right := GaussianGammaAdjacentCutoff.multiply_cross f f (GaussianNamedGamma.nameF f) (nameF f)
    x x (data x A) (data x A) h.andE₁ h.andE₁ (GaussianNamedGamma.name_regular f x A h) (name_regular f x A h)
    (cross_refl _ _ h.andE₁) (cross_symm _ _ _ _ eq)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ recurrence right)

theorem actual_original_named_Euler_integral_IBP_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶
        crossEquivalent (nameF (shiftF f)) (productF f) (data (shiftData (var 0)) (var 1)) (productData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_named_Euler_IBP_recurrence f _ _ Prf.hyp0))

theorem actual_original_named_Euler_integral_IBP_independent_queries_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 2) (var 3) ⟶
        distanceBounded (ap2 (nameF (shiftF f)) (var 0) (data (shiftData (var 2)) (var 3)))
          (ap2 (productF f) (var 1) (productData f (var 2) (var 3)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (.impI (cross_at _ _ _ _ _ _ (original_named_Euler_IBP_recurrence f _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedIntegralIBPRecurrence
