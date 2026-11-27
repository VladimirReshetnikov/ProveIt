import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondDerivativeBinding
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.Cofinal.GaussianBarnesCanonicalThirdDerivativeCofinalBinding

/-! The original positive Barnes logarithm has three successive derivative names on the
same certified chart. The third derivative is the original cofinal cubic series. -/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmCalculus

open_ipra
open Common
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "chart" => GaussianBarnesCanonicalThirdDerivativeCofinalBinding.source
local notation "L₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "d₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.data
local notation "L₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.nameF
local notation "d₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.data
local notation "L₃" => GaussianBarnesCanonicalThirdLogarithmCofinal.nameF
local notation "d₃" => GaussianBarnesCanonicalThirdLogarithmCofinal.data
local notation "Q₁" => GaussianBarnesCanonicalPositiveLogarithmDerivative.quotientF
local notation "q₁" => GaussianBarnesCanonicalPositiveLogarithmDerivative.quotientData
local notation "Q₂" => GaussianBarnesCanonicalPositiveSecondDerivativeBinding.quotientF
local notation "q₂" => GaussianBarnesCanonicalPositiveSecondDerivativeBinding.quotientData
local notation "Q₃" => GaussianBarnesCanonicalThirdDerivativeCofinalBinding.quotientF
local notation "q₃" => GaussianBarnesCanonicalThirdDerivativeCofinalBinding.quotientData
local notation "g₂" => GaussianBarnesCanonicalPositiveSecondDerivativeBinding.quotientNumerator
local notation "g₃" => GaussianBarnesCanonicalThirdDerivativeCofinalBinding.quotientNumerator
local notation "firstBudget" => GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative.budget

def budget (p R K : PTm n) : PTm n :=
  firstBudget p R K+(num 4*(K*K*K)+num 12*(K*K*K*K))*unit p

def source (p A C B R K : PTm n) : Fm PTm n :=
  let h := step A C
  let H := GaussianL1.norm1 h
  chart A C B R H K ⋏ (le one (normSq h) ⋏ le (budget p R K*H) B)

def rates (p A C B R : PTm n) : Fm PTm n :=
  independentRate Q₁ L₁ (q₁ A C B R R) (d₁ A B R) one (unit p) ⋏
    (independentRate Q₂ L₂ (q₂ A C B R) (d₂ A B R) one (unit p) ⋏
      independentRate Q₃ L₃ (q₃ A C B R) (d₃ A B) one (unit p))

theorem dyadic_rates (p A C B R K : PTm n) (h : Γ ⊢[PRAAx] source p A C B R K) :
    Γ ⊢[PRAAx] rates p A C B R := by
  let H := GaussianL1.norm1 (step A C)
  let U := unit p
  let V := firstBudget p R K
  let M := num 4*(K*K*K)
  let N := num 12*(K*K*K*K)
  let T := budget p R K
  have hb := h.andE₁.andE₁.andE₁
  have hs := h.andE₁
  have hn := h.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have target : Γ ⊢[PRAAx] le (T*H) B := h.andE₂.andE₂
  have firstGuard : Γ ⊢[PRAAx] le (V*H) B :=
    le_trans (mul_le_mul_right H (le_add_right V ((M+N)*U))) target
  have secondGuard : Γ ⊢[PRAAx] le (g₂ H K*U) (one*B) := by
    have cap : Γ ⊢[PRAAx] le (M*U) T :=
      le_trans (mul_le_mul_right U (le_add_right M N)) (le_add_left ((M+N)*U) V)
    exact le_congr (by dsimp only [M,GaussianBarnesCanonicalPositiveSecondDerivativeBinding.quotientNumerator]; ipra_ring)
      (one_mul B).eqSymm (le_trans (mul_le_mul_right H cap) target)
  have thirdGuard : Γ ⊢[PRAAx] le (g₃ H K*U) (one*B) := by
    have cap : Γ ⊢[PRAAx] le (N*U) T :=
      le_trans (mul_le_mul_right U (le_add_left N M)) (le_add_left ((M+N)*U) V)
    exact le_congr (by dsimp only [N,GaussianBarnesCanonicalThirdDerivativeCofinalBinding.quotientNumerator]; ipra_ring)
      (one_mul B).eqSymm (le_trans (mul_le_mul_right H cap) target)
  have first := GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative.dyadic_rate p A C B R K
    (.andI hs (.andI hn firstGuard))
  have second := GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hb hU secondGuard
    (GaussianBarnesCanonicalPositiveSecondDerivativeBinding.quotient_rate A C B R K hs hn)
  have third := GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hb hU thirdGuard
    (GaussianBarnesCanonicalThirdDerivativeCofinalBinding.quotient_rate A C B R K hs hn)
  exact .andI first (.andI second third)

theorem actual_Barnes_positive_logarithm_three_derivatives_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let p := var 0
       let A := var 1
       let C := var 2
       let B := var 3
       let R := var 4
       let K := var 5
       source p A C B R K ⟶ rates p A C B R) :=
  closeUniv 6 (.impI (dyadic_rates _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmCalculus
