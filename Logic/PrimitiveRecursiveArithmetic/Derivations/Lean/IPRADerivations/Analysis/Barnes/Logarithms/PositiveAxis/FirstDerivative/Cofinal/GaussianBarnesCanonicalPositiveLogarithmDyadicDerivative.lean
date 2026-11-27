import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveLogarithmDerivative
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveRelativeLogarithmChart

/-! An explicit dyadic derivative modulus for the original positive Barnes logarithm
on a common disk and away from the origin. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative

open_ipra
open Common
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalPositiveRelativeLogarithmChart (threshold)
open GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative (gain)
open GaussianBarnesCanonicalPositiveLogarithmDerivative (quotientF quotientData quotientNumerator)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "F" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "fd" => GaussianBarnesCanonicalPositiveFirstLogarithm.data

def budget (p R K : PTm n) : PTm n := (threshold R K+two*gain R K)*unit p

def source (p A C B R K : PTm n) : Fm PTm n :=
  let h := step A C
  let H := GaussianL1.norm1 h
  (GaussianBarnesCanonicalThirdDerivativePositiveMargin.source A C B H K ⋏
    (disk (center A B) R B ⋏ disk (center C B) R B)) ⋏
  (le one (normSq h) ⋏ le (budget p R K*H) B)

theorem dyadic_rate (p A C B R K : PTm n) (h : Γ ⊢[PRAAx] source p A C B R K) : Γ ⊢[PRAAx]
    independentRate quotientF F (quotientData A C B R R) (fd A B R) one (unit p) := by
  let H := GaussianL1.norm1 (step A C)
  let T := threshold R K
  let G := two*gain R K
  let U := unit p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hmargin := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have hc := h.andE₁.andE₂.andE₂
  have hn := h.andE₂.andE₁
  have m : Γ ⊢[PRAAx] le (budget p R K*H) B := h.andE₂.andE₂
  have a : Γ ⊢[PRAAx] le T ((T+G)*U) :=
    le_congr (by ipra_ring) (.eqRefl _) (Common.mul_le_mul (le_add_right T G) hU)
  have b : Γ ⊢[PRAAx] le (G*U) ((T+G)*U) :=
    Common.mul_le_mul (le_add_left G T) (le_refl U)
  have small : Γ ⊢[PRAAx] le (T*H) B := le_trans (mul_le_mul_right H a) m
  have rad : Γ ⊢[PRAAx] le (quotientNumerator R H K*U) (one*B) :=
    le_congr (by dsimp only [G,quotientNumerator]; ipra_ring) (one_mul B).eqSymm
      (le_trans (mul_le_mul_right H b) m)
  have hs := GaussianBarnesCanonicalPositiveRelativeLogarithmChart.admission A C B R H K hmargin ha hc small
  have raw := GaussianBarnesCanonicalPositiveLogarithmDerivative.quotient_rate A C B R R K
    (.andI hmargin hs) (.andI hmargin.andE₂.andE₂.andE₁ hc) hn
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hmargin.andE₁ hU rad raw

theorem actual_Barnes_positive_logarithm_first_derivative_dyadic_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let p := var 0
       let A := var 1
       let C := var 2
       let B := var 3
       let R := var 4
       let K := var 5
       source p A C B R K ⟶ independentRate quotientF F (quotientData A C B R R) (fd A B R) one (unit p)) :=
  closeUniv 6 (.impI (dyadic_rate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative
