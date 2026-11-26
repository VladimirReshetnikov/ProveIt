import IPRADerivations.Analysis.Euler.Logarithms.LowerBounds.GaussianEulerLogarithmicNamedLowerBound

/-!
# A genuine dyadic cutoff for the original logarithmic lower tail

The exact factorial coefficient j!(2A)^(j+1) is paid by the original
FastValueCut clock. Any later first cutoff and any later second cutoff
retain the same original compact logarithmic observation and satisfy
2^-(k+6)+2^-p. The numerical schedule is independent of the interval's
finer second cutoff. It may be combined with an enlarged upper schedule.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerCutoffBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicNamedLowerBound (source leading point)
open GaussianEulerLogarithmicLowerRootRows (panelDegree)
open GaussianGammaIntegralCutoffs (height)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (k j A : PTm n) : PTm n := GaussianFastValueCut.exponent (leading j A) (k+num 6)
def scheduledData (j z R B k q A : PTm n) : PTm n :=
  GaussianEulerLogarithmicNamedLowerBound.data j z R B (clock k j A) q A

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (k j A : PTm n) :
    Syn.subst σ (clock k j A) = clock (Syn.subst σ k) (Syn.subst σ j) (Syn.subst σ A) := by simp [clock]
@[simp] theorem subst_scheduledData {m : ℕ} (σ : Fin n → PTm m) (j z R B k q A : PTm n) :
    Syn.subst σ (scheduledData j z R B k q A) = scheduledData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ q) (Syn.subst σ A) := by simp [scheduledData]

theorem clock_later (k j A : PTm n) : Γ ⊢[PRAAx] le k (clock k j A) :=
  le_trans (le_add_right k (num 6)) (le_add_right _ _)

theorem original_coefficient_budget (k j p A R : PTm n) (hk : Γ ⊢[PRAAx] le (clock k j A) p) : Γ ⊢[PRAAx]
    le (leading j A*unit (k+num 6)) (unit (height p (panelDegree A) R)) := by
  have step : Γ ⊢[PRAAx] le (clock k j A) (height p (panelDegree A) R) :=
    le_trans hk (le_trans (le_add_right p (panelDegree A))
      (le_trans (le_add_right _ (GaussianGammaIntegralCutoffs.tailCoefficient R)) (le_add_right _ (num 10))))
  exact le_trans (GaussianFastValueCut.query_budget (leading j A) (k+num 6))
    (GaussianExponentialReference.unit_monotone step)

/-- No replacement of the original compact program or its requested
precision is made. Both cutoffs may be arbitrarily later. -/
theorem original_cutoff_tail_bound (s j z R B k p q A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hk : Γ ⊢[PRAAx] le (clock k j A) p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    bounded (point s j z R B p q A) (unit s+unit (k+num 6)) (unit (k+num 6)*unit s) := by
  have actual := GaussianEulerLogarithmicNamedLowerBound.original_named_bound s j z R B p q A h hpq
  have budget := original_coefficient_budget k j p A R hk
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive (height p (panelDegree A) R)) (unit_positive s))
    (positive_product _ _ (unit_positive (k+num 6)) (unit_positive s)) _ actual
  unfold GaussianEulerLogarithmicNamedLowerBound.numerator
  ipra_le (𝔞(unit s))^2*sl budget

theorem original_scheduled_tail_bound (s j z R B k q A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hq : Γ ⊢[PRAAx] le (clock k j A) q) : Γ ⊢[PRAAx]
    bounded (point s j z R B (clock k j A) q A) (unit s+unit (k+num 6)) (unit (k+num 6)*unit s) :=
  original_cutoff_tail_bound s j z R B k (clock k j A) q A h (le_refl _) hq

theorem original_logarithmic_lower_tail_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 2) (var 3) (var 4) (var 8) ⋏
      (le (clock (var 5) (var 1) (var 8)) (var 6) ⋏ le (var 6) (var 7))) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) (var 8))
        (unit (var 0)+unit (var 5+num 6)) (unit (var 5+num 6)*unit (var 0))) :=
  closeUniv 9 (.impI (original_cutoff_tail_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerCutoffBudget
