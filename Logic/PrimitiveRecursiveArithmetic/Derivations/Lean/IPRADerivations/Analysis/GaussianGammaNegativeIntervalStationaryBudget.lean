import IPRADerivations.Analysis.GaussianGammaNegativeIntervalLogCenterVariation

/-!
# A base-independent stationary error coefficient for negative Gamma

The derivative residual has a requested dyadic precision. Choose the
thin chord later according to the literal derivative error coefficient.
This leaves the stationary bound independent of the rational encoding
and preserves the separation term in the logarithm comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalStationaryBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent exponent_unit normalizer query_budget)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalChordInverse (poleMargin)
open GaussianGammaNegativeIntervalChordRate (cost)
open GaussianGammaNegativeIntervalLogAbsoluteRetiming (margin)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (qadd)
open RationalValueBounds (upper upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "T" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "td" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "ld" => GaussianGammaNegativeIntervalLogAbsolute.nameData
local notation "g" => GaussianGammaNegativeIntervalLogThinChord.margin

def comparisonCost (N C : PTm n) : PTm n := margin N*(C+one)

theorem stationary_at (p q k a c b N K C z : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (unit k)) : Γ ⊢[PRAAx]
    upper (fstT (qadd (g a c b) (ap2 L p (ld a b N)))) (fstT (ap2 L q (ld c b N)))
      (rateNumerator (comparisonCost N C) (unit k) p q) (rateDenominator (unit k) p q) := by
  let H := cost a b N K
  let r := exponent H k
  let v := unit (normalizer H)
  have er : Γ ⊢[PRAAx] unit r ≐ unit k*v := exponent_unit H k
  have e := natEq er
  have hk := unit_positive (Γ := Γ) k
  have hr := unit_positive (Γ := Γ) r
  have lifted := GaussianNamedRateRadius.weaken T zeroF (td a b N) z C (unit k) (C*v) (unit r) hk hr
    (by ipra_le 0 using linear_combination -𝔞(C)*e) residual
  have h := GaussianGammaNegativeIntervalLogCenterVariation.stationary_at p q r a c b N K (C*v) z ha hc apart hma hmc lifted
  have hPay : Γ ⊢[PRAAx] le (H*unit k) (unit r) := query_budget H k
  apply upper_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive (unit r) p q hr) h
  dsimp only [rateNumerator,rateDenominator,comparisonCost,GaussianGammaNegativeIntervalLogCenterVariation.rateCost]
  change Γ ⊢[PRAAx] le ((margin N*(H+C*v)*unit p*unit q+unit r*(unit p+unit q))*(unit k*unit p*unit q))
    ((margin N*(C+one)*unit p*unit q+unit k*(unit p+unit q))*(unit r*unit p*unit q))
  ipra_le 𝔞(margin N)*(𝔞(unit p)*𝔞(unit q))^2*sl hPay using
    linear_combination 𝔞(margin N)*(𝔞(unit p)*𝔞(unit q))^2*𝔞(C)*e

theorem actual_original_negative_interval_uniform_stationary_at_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((guard (var 3) (var 5) ⋏ (guard (var 4) (var 5) ⋏ ((lt (var 3) (var 4) ⋎ lt (var 4) (var 3)) ⋏
         (poleMargin (var 3) (var 5) (var 7) ⋏ poleMargin (var 4) (var 5) (var 7))))) ⟶
       independentRate T zeroF (td (var 3) (var 5) (var 6)) (var 9) (var 8) (unit (var 2)) ⟶
       upper (fstT (qadd (g (var 3) (var 4) (var 5)) (ap2 L (var 0) (ld (var 3) (var 5) (var 6)))))
          (fstT (ap2 L (var 1) (ld (var 4) (var 5) (var 6))))
         (rateNumerator (comparisonCost (var 6) (var 8)) (unit (var 2)) (var 0) (var 1))
         (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 10 (.impI (.impI (stationary_at _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalStationaryBudget
