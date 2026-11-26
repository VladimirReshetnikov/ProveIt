import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.GaussianGammaNegativeIntervalCriticalResidualRate
import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.GaussianGammaNegativeIntervalStationaryBudget

/-!
# Negative Gamma comparison at the selected critical approximants

The actual selected rational has a certified derivative residual.
At every other rational with the same denominator and a common pole
margin, the original log magnitude satisfies the strong comparison
with an error tending to zero along the selection schedule.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalGrid (denominator grid_guard leftIndex numerator room selected)
open GaussianGammaNegativeCriticalLocation (lower)
open GaussianGammaNegativeIntervalChordInverse (poleMargin)
open GaussianGammaNegativeIntervalCriticalDerivativeZero (argumentNumerator argumentDenominator locationClock)
open GaussianGammaNegativeIntervalCriticalQuotientZero (stage)
open GaussianGammaNegativeIntervalStationaryBudget (comparisonCost)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalHorner (qadd qzero)
open RationalValueBounds (upper)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "ld" => GaussianGammaNegativeIntervalLogAbsolute.nameData
local notation "g" => GaussianGammaNegativeIntervalLogThinChord.margin

theorem base_guard (k N : PTm n) : Γ ⊢[PRAAx] guard (argumentNumerator k N) (argumentDenominator k N) := by
  let s := locationClock k N
  exact grid_guard s N (leftIndex s N) (le_of_lt (selected s N).andE₁)

theorem base_margin (k N K : PTm n) (hK : Γ ⊢[PRAAx] le (mesh N) K) :
    Γ ⊢[PRAAx] poleMargin (argumentNumerator k N) (argumentDenominator k N) K := by
  let s := locationClock k N
  let a := argumentNumerator k N
  let b := argumentDenominator k N
  let i := leftIndex s N
  have hs := le_of_lt (selected (Γ := Γ) s N).andE₁
  have edge : Γ ⊢[PRAAx] le (a+unit s) b := room s N i hs
  have e := natEq (eq_add_of_le (le_of_lt (base_guard (Γ := Γ) k N).andE₂))
  have gap : Γ ⊢[PRAAx] le (unit s) (monus b a) := by ipra_le sl edge with -e
  have eq : Γ ⊢[PRAAx] b ≐ unit s*mesh N := .eqRefl _
  have h : Γ ⊢[PRAAx] le b (K*unit s) :=
    le_congr ((mul_comm _ _).eqTrans eq.eqSymm) (.eqRefl _) (mul_le_mul_right (unit s) hK)
  have step : Γ ⊢[PRAAx] le (K*unit s) (K*monus b a) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right K gap)
  have left : Γ ⊢[PRAAx] le (K*unit s) (K*a) := by
    change Γ ⊢[PRAAx] le (K*unit s) (K*(unit s+i))
    ipra_le 𝔞(K)*𝔞(i)
  exact .andI (le_trans h left) (le_trans h step)

theorem selected_comparison (p q k c N K : PTm n)
    (hc : Γ ⊢[PRAAx] guard c (argumentDenominator k N))
    (apart : Γ ⊢[PRAAx] lt (argumentNumerator k N) c ⋎ lt c (argumentNumerator k N))
    (hK : Γ ⊢[PRAAx] le (mesh N) K) (hm : Γ ⊢[PRAAx] poleMargin c (argumentDenominator k N) K) : Γ ⊢[PRAAx]
    upper (fstT (qadd (g (argumentNumerator k N) c (argumentDenominator k N))
      (ap2 L p (ld (argumentNumerator k N) (argumentDenominator k N) N))))
      (fstT (ap2 L q (ld c (argumentDenominator k N) N)))
      (rateNumerator (comparisonCost N two) (unit (stage k)) p q) (rateDenominator (unit (stage k)) p q) :=
  GaussianGammaNegativeIntervalStationaryBudget.stationary_at p q (stage k) (argumentNumerator k N) c
    (argumentDenominator k N) N K two qzero (base_guard k N) hc apart (base_margin k N K hK) hm
    (GaussianGammaNegativeIntervalCriticalResidualRate.original_rate k N)

theorem actual_original_negative_interval_selected_comparison_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 3) (argumentDenominator (var 2) (var 4)) ⋏
        ((lt (argumentNumerator (var 2) (var 4)) (var 3) ⋎ lt (var 3) (argumentNumerator (var 2) (var 4))) ⋏
          (le (mesh (var 4)) (var 5) ⋏ poleMargin (var 3) (argumentDenominator (var 2) (var 4)) (var 5)))) ⟶
        upper (fstT (qadd (g (argumentNumerator (var 2) (var 4)) (var 3) (argumentDenominator (var 2) (var 4)))
          (ap2 L (var 0) (ld (argumentNumerator (var 2) (var 4)) (argumentDenominator (var 2) (var 4)) (var 4)))))
          (fstT (ap2 L (var 1) (ld (var 3) (argumentDenominator (var 2) (var 4)) (var 4))))
          (rateNumerator (comparisonCost (var 4) two) (unit (stage (var 2))) (var 0) (var 1))
          (rateDenominator (unit (stage (var 2))) (var 0) (var 1))) :=
  closeUniv 6 (.impI (selected_comparison _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalComparison
