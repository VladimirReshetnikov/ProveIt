import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerLinearSlopeProduct
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerTaylorRows

/-!
# The first-order approximation of the finite Euler logarithm

The original finite Euler head increment differs from the displacement
times the original finite slope by a quadratic remainder and explicit
observation slack.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorFinite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerLinearSlope (sum_value)
open GaussianLogGammaEulerLinearSlopeProduct (original_increment_at)
open GaussianLogGammaEulerTaylorRows (coefficient errorDenominator named_sum_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRightHalfPlaneLogarithmIncrementBound (input)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "headF" => GaussianLogGammaEulerHead.nameF
local notation "headData" => GaussianLogGammaEulerHead.data
local notation "slopeF" => GaussianLogGammaEulerLinearSlopeProduct.nameF
local notation "slopeData" => GaussianLogGammaEulerLinearSlopeProduct.data

def errorNumerator (p D H K : PTm n) : PTm n :=
  coefficient H K * unit p + num 25 * (D * D)

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (p D H K : PTm n) :
    Syn.subst σ (errorNumerator p D H K) =
      errorNumerator (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ H) (Syn.subst σ K) := by
  simp [errorNumerator, coefficient]

theorem sample_error (p A B neg a b sign D H J M K N : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K * A))
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 headF p (headData a b D sign N)) (ap2 headF p (headData A B D neg N)))
      (ap2 slopeF p (slopeData A B neg a b sign D N))
      (errorNumerator p D H K) (errorDenominator p D) := by
  have hBase := h.andE₁.andE₁
  have hLater := h.andE₁.andE₂.andE₁
  have hD := hBase.andE₂
  have hu := unit_positive (Γ := Γ) p
  have hd := positive_product D D hD hD
  have he := positive_product (D * D) (unit p) hd hu
  have rows := distance_congr (.eqRefl _) (sum_value A B neg a b sign D N).eqSymm
    (.eqRefl _) (.eqRefl _) (named_sum_error p A B neg a b sign D H J M K N h hK)
  have transported := original_increment_at p A B neg a b sign D N _ _ hBase hLater hN he rows
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ he hu) he
    (le_of_eq_add (d := zero) (by
      unfold errorNumerator errorDenominator GaussianLogGammaEulerTaylorRows.errorNumerator
      ipra_ring)) transported

theorem actual_finite_Euler_logarithm_Taylor_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (input (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        le (var 7) (var 11 * var 1) ⟶ le one (var 12) ⟶
        distanceBounded
          (qsub (ap2 headF (var 0) (headData (var 4) (var 5) (var 7) (var 6) (var 12)))
            (ap2 headF (var 0) (headData (var 1) (var 2) (var 7) (var 3) (var 12))))
          (ap2 slopeF (var 0)
            (slopeData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 12)))
          (errorNumerator (var 0) (var 7) (var 8) (var 11)) (errorDenominator (var 0) (var 7))) :=
  closeUniv 13 (.impI (.impI (.impI (sample_error _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorFinite
