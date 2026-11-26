import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianDiscreteDerivativeRounding
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteThirdDerivativeNormalization

/-!
# Four actual Gaussian observations from three finite derivative rates

Use one common rounding denominator for the original function and
derivative observations. Three coded Gaussian finite quotient rates
and a signed floor on the rounded third derivative give the stated
bound on the actual four coarse observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianDiscreteThirdDerivativeEstimate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDiscreteDerivativeRounding (allowance body latticeScale signed_source source sample_at)
open GaussianSignedObservationGrid (rounded)
open SignedDiscreteDerivativeOperators (width divisor)
open SignedDiscreteThirdDerivativeEstimate (window)
open SignedDiscreteDerivativeBounds (floorOn)
open SignedDiscreteThirdDerivativeNormalization (stencil budget normalized_lower)
open SignedCubicTaylorGrid (combination)
open PolynomialBisection (zle_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fourObservations (f : PTm 2) (x i : PTm n) : ZT n :=
  let j := i+width x
  let k := j+width x
  let l := k+width x
  let S := latticeScale x
  combination (rounded (inst2 f i x) S) (rounded (inst2 f j x) S)
    (rounded (inst2 f k x) S) (rounded (inst2 f l x) S)

def comparisonBudget (x N T E₀ E₁ E₂ : PTm n) : PTm n :=
  budget N T (allowance (divisor x) E₀) (allowance (divisor x) E₁) (allowance (divisor x) E₂)

theorem four_observations_lower (f g h j : PTm 2) (x i N T E₀ E₁ E₂ : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hS : Γ ⊢[PRAAx] le one (latticeScale x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (h₀ : Γ ⊢[PRAAx] source f g x (window x i) E₀)
    (h₁ : Γ ⊢[PRAAx] source g h x (window x i) E₁)
    (h₂ : Γ ⊢[PRAAx] source h j x (window x i) E₂)
    (hj : Γ ⊢[PRAAx] floorOn (body j) x (window x i) T) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (comparisonBudget x N T E₀ E₁ E₂))
      (ZT.ofNat (N*(N*N))*fourObservations f x i) := by
  have raw := normalized_lower (body f) (body g) (body h) (body j) x i N T _ _ _ hM hD
    (signed_source f g _ _ E₀ hS h₀) (signed_source g h _ _ E₁ hS h₁)
    (signed_source h j _ _ E₂ hS h₂) hj
  exact zle_congr rfl (by rw [show stencil (body f) x i = fourObservations f x i by
    simp only [stencil,fourObservations,sample_at]]) raw

theorem actual_Gaussian_four_observation_derivative_bound_closed (f g h j : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let x := var 0
       let i := var 1
       let N := var 2
       let T := var 3
       let E₀ := var 4
       let E₁ := var 5
       let E₂ := var 6
       le one (width x) ⟶ le one (latticeScale x) ⟶ divisor x ≐ N*width x ⟶
         source f g x (window x i) E₀ ⟶ source g h x (window x i) E₁ ⟶
           source h j x (window x i) E₂ ⟶ floorOn (body j) x (window x i) T ⟶
             zle (-ZT.ofNat (comparisonBudget x N T E₀ E₁ E₂))
               (ZT.ofNat (N*(N*N))*fourObservations f x i)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (four_observations_lower f g h j _ _ _ _ _ _ _
      Prf.hyp1.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))))

end LeanProofs.IPRA.Analysis.GaussianDiscreteThirdDerivativeEstimate
