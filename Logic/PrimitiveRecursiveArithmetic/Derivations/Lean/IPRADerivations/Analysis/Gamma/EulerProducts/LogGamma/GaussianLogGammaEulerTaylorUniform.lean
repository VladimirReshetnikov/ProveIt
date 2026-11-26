import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerTaylorCofinal
import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmIncrementMargin

/-!
# Canonical log-Gamma Taylor bound on a certified rational rectangle

Margins and a common size bound give a uniform small-displacement
condition. The auxiliary radial and angle certificates are computed
from the two endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorUniform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerTaylorCofinal (incrementF incrementData weightedF weightedData)
open GaussianLogGammaEulerTaylorRows (coefficient)
open GaussianNamedInverseRate (independentRate)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep admitted)
open GaussianRootAlgebra (sub)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Src" => GaussianRightHalfPlaneLogarithm.source

def source (A B neg a b sign D H K C : PTm n) : Fm PTm n :=
  Src A D neg ⋏ (Src a D sign ⋏
    (ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) H ⋏
      (le one K ⋏ (le D (K*A) ⋏ (le D (K*a) ⋏ (le (A+B+a+b) (C*D) ⋏ smallStep H K C D))))))

theorem independent_rate (A B neg a b sign D H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A B neg a b sign D H K C) :
    Γ ⊢[PRAAx] independentRate incrementF weightedF (incrementData A B neg a b sign D)
      (weightedData A B neg a b sign D) (coefficient H K) (D*D) := by
  have hK := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have guard := admitted A B neg a b sign D H K C h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₁ hK h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  exact GaussianLogGammaEulerTaylorCofinal.independent_rate A B neg a b sign D H _ _ K guard hK

theorem actual_uniform_cofinal_log_Gamma_Taylor_estimate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        independentRate incrementF weightedF
          (incrementData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (weightedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (coefficient (var 7) (var 8)) (var 6*var 6)) :=
  closeUniv 10 (.impI (independent_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorUniform
