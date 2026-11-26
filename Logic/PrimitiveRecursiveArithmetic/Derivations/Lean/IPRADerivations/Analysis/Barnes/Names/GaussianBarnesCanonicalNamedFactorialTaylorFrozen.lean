import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFactorialTaylor

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
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R e : PTm n) :
    Syn.subst σ (clock p R e) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ e) := by
  simp [clock]

private theorem frozen_budget (p q s a : PTm n)
    (h : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] le (rateNumerator one (unit a) (succ p) q*rateDenominator (unit s) p q)
      (rateNumerator one (unit s) p q*rateDenominator (unit a) (succ p) q) := by
  let P := unit p
  let Q := unit q
  let S := unit s
  let W := unit a
  have cleared : Γ ⊢[PRAAx]
      le ((one*(two*P)*Q+W*(two*P+Q))*(S*P*Q)) ((one*P*Q+S*(P+Q))*(W*(two*P)*Q)) := by
    change Γ ⊢[PRAAx] le (two*P*S) (W*(two*P+S)) at h
    ipra_le 𝔞(P)*𝔞(Q)^2*sl h
  have double : Γ ⊢[PRAAx] unit (succ p) ≐ two*P := (pw_succ two p).eqTrans (mul_comm _ _)
  exact le_congr
    (congrMul (congrAdd (congrMul (congrMul (.eqRefl _) double) (.eqRefl _))
      (congrMul (.eqRefl _) (congrAdd double (.eqRefl _)))) (.eqRefl _)).eqSymm
    (congrMul (.eqRefl _) (congrMul (congrMul (.eqRefl _) double) (.eqRefl _))).eqSymm cleared

private theorem read_with (f : PR 2) (p q s a k x R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R e) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s))
    (hb : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R e)) (ap2 F q (frozenData f k x R e))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let r := clock p R e
  have rate := late_rate f f a r k x x R e hf hf (cross_refl _ _ hf.andE₁)
    (Common.succ_le_succ (inputClock_monotone R e a (succ p) hp))
    (le_trans (Common.succ_le_succ (inputClock_monotone R e a (succ s) hs)) hk)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive a))
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget p q s a hb)
    (rate_at _ _ _ _ _ _ (succ p) q rate)
  exact distance_congr (sample_at f p x R e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_observations (f : PR 2) (p q s k x R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R e) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R e)) (ap2 F q (frozenData f k x R e))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  refine .orE (le_total p s) ?_ ?_
  · have lp : le p s :: Γ ⊢[PRAAx] le (succ p) (succ s) :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one Prf.hyp0)
    have double : le p s :: Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
    have hb : le p s :: Γ ⊢[PRAAx] le (two*unit p*unit s) ((two*unit p)*(two*unit p+unit s)) :=
      le_of_eq_add (d := two*unit p*(two*unit p)) (by ipra_ring)
    exact read_with f p q s (succ p) k x R e hf.wk hk.wk (le_refl _) lp
      (le_congr (.eqRefl _) (congrMul double.eqSymm (.eqRefl _)) hb)
  · have hb : le s p :: Γ ⊢[PRAAx] le (two*unit p*unit s) (unit s*(two*unit p+unit s)) :=
      le_of_eq_add (d := unit s*unit s) (by ipra_ring)
    exact read_with f p q s s k x R e hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s) hb

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
