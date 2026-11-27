import IPRADerivations.Analysis.Barnes.Names.FactorialTaylor.GaussianBarnesCanonicalNamedFactorialTaylor
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Late rational readback of the named Barnes factorial Taylor evaluator

At each sufficiently late input clock the original rational evaluator
at the observed point approximates the named factorial Taylor sampler.
The rate keeps the output clocks independent of the frozen input clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorFrozen

open_ipra
open GaussianBarnesCanonicalNamedDemand (source)
open GaussianBarnesCanonicalNamedFactorialTaylor (nameF data frozenData clock sample_at late_rate)
open GaussianBarnesCanonicalTaylorDerivativeUniformInput (inputClock_monotone)
open GaussianCoefficientNameBounds (unit)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedRateRadius (frozen_observation_of_rates)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R e : PTm n) :
    Syn.subst σ (clock p R e) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ e) := by
  simp [clock]

private theorem late_frozen_rate (f : PR 2) (p s a k x R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R e) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s)) :
    Γ ⊢[PRAAx] independentRate F F (frozenData f (clock p R e) x R e) (frozenData f k x R e) one (unit a) :=
  late_rate f f a (clock p R e) k x x R e hf hf (cross_refl _ _ hf.andE₁)
    (Common.succ_le_succ (inputClock_monotone R e a (succ p) hp))
    (le_trans (Common.succ_le_succ (inputClock_monotone R e a (succ s) hs)) hk)

theorem frozen_observations (f : PR 2) (p q s k x R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R e) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R e)) (ap2 F q (frozenData f k x R e))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  have read := frozen_observation_of_rates F F p q s (frozenData f (clock p R e) x R e) (frozenData f k x R e)
    (late_frozen_rate f p s (succ p) k x R e hf.wk hk.wk (le_refl _) (Common.succ_le_succ Prf.hyp0))
    (late_frozen_rate f p s s k x R e hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s))
  exact distance_congr (sample_at f p x R e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) read

theorem frozen_rate (f : PR 2) (s k x R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R e) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) F (data x R e) (frozenData f k x R e) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have later : Δ ⊢[PRAAx] le (clock (sh s) (sh R) (sh e)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate,GaussianBarnesCanonicalNamedFactorialTaylor.subst_data,GaussianBarnesCanonicalNamedFactorialTaylor.subst_frozenData,
    GaussianCoefficientNameBounds.subst_unit,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
      frozen_observations f (var 1) (var 0) (sh s) (sh k) (sh x) (sh R) (sh e) h later

theorem actual_named_Barnes_factorial_Taylor_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF f) F (data (var 0) (var 1) (var 2))
          (frozenData f (var 4) (var 0) (var 1) (var 2)) one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (frozen_rate f _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorFrozen
