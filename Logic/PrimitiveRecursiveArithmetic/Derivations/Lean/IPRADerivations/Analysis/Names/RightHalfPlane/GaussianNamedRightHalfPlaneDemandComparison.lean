import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneDemandLift

/-!
# Compare demand-based right-half-plane lifts

Each lift agrees with rational evaluations frozen at every sufficiently
late actual input observation. Two maps with the same input demand also
agree on regular names whenever their rational evaluations agree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneDemandComparison

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedRightHalfPlaneLift (source data late_certificate subst_source subst_data)
open GaussianNamedRightHalfPlaneDemandLift (RationalMap demandBody clock frozenData sample nameF
  subst_clock subst_frozenData sample_at clock_margin clock_demand late_rate name_regular)
open GaussianNamedRightHalfPlaneSigned (certificate)
open GaussianNameEquivalence (crossEquivalent diagonalEquivalent diagonal_to_cross
  cross_to_diagonal diagonal_at cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem frozen_budget (p q s a : PTm n)
    (h : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) : Γ ⊢[PRAAx]
    le (rateNumerator one (unit a) (succ p) q*rateDenominator (unit s) p q)
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

private theorem rate_with (map : RationalMap) (f : PR 2) (p q s a k x M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s))
    (hb : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x M R))
      (ap2 map.evaluator q (frozenData map f k x M R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let r := clock map p M R
  have rate := late_rate map f f a r k x x M R hf hf (cross_refl _ _ hf.andE₁.andE₁)
    (clock_margin map p M R) (le_trans (clock_margin map s M R) hk)
    (clock_demand map p M R a hp) (le_trans (clock_demand map s M R a hs) hk)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive a))
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget p q s a hb)
    (rate_at _ _ _ _ _ _ (succ p) q rate)
  exact distance_congr (sample_at map f p x M R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_observations (map : RationalMap) (f : PR 2) (p q s k x M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x M R))
      (ap2 map.evaluator q (frozenData map f k x M R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  refine .orE (le_total p s) ?_ ?_
  · have late : le p s :: Γ ⊢[PRAAx] le (succ p) (succ s) :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one Prf.hyp0)
    have double : le p s :: Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
    have hb : le p s :: Γ ⊢[PRAAx] le (two*unit p*unit s) ((two*unit p)*(two*unit p+unit s)) :=
      le_of_eq_add (d := two*unit p*(two*unit p)) (by ipra_ring)
    exact rate_with map f p q s (succ p) k x M R hf.wk hk.wk (le_refl _) late
      (le_congr (.eqRefl _) (congrMul double.eqSymm (.eqRefl _)) hb)
  · have hb : le s p :: Γ ⊢[PRAAx] le (two*unit p*unit s) (unit s*(two*unit p+unit s)) :=
      le_of_eq_add (d := unit s*unit s) (by ipra_ring)
    exact rate_with map f p q s s k x M R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s) hb

theorem frozen_rate (map : RationalMap) (f : PR 2) (s k x M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF map f) map.evaluator (data x M R) (frozenData map f k x M R)
      one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : Δ ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have late : Δ ⊢[PRAAx] le (clock map (sh s) (sh M) (sh R)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate,subst_data,subst_frozenData,GaussianCoefficientNameBounds.subst_unit,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
    frozen_observations map f (var 1) (var 0) (sh s) (sh k) (sh x) (sh M) (sh R) h late

theorem equal_of_rational_agreement (map other : RationalMap) (sameDemand : map.demand = other.demand)
    (agree : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (z R K : PTm m), (Δ ⊢[PRAAx] certificate z R K) →
      (Δ ⊢[PRAAx] crossEquivalent map.evaluator other.evaluator
        (ap3 map.rationalData z R K) (ap3 other.rationalData z R K)))
    (f : PR 2) (x M R : PTm n) (hf : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF map f) (nameF other f) (data x M R) (data x M R) := by
  apply diagonal_to_cross _ _ _ _ (name_regular map f x M R hf) (name_regular other f x M R hf)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let s := Syn.shift x
  let A := Syn.shift M
  let B := Syn.shift R
  let p : PTm (n+1) := var 0
  let k := clock map p A B
  have hs : Δ ⊢[PRAAx] source f s A B := by simpa [Δ,s,A,B,Fm.shift,Syn.shift] using hf.shift
  have otherClock : clock other p A B = k := by simp [k,clock,demandBody,sameDemand]
  have same := agree (ap2 f k s) B (two*A) (late_certificate f s k A B hs (clock_margin map p A B))
  have obs := diagonal_at _ _ _ _ (succ p) (cross_to_diagonal _ _ _ _ same)
  have budget : Δ ⊢[PRAAx] le (two*unit p) (two*unit (succ p)) :=
    mul_le_mul_left two (unit_monotone (le_succ_self p))
  have near := distance_radius_mono _ _ _ _ _ _ (unit_positive (succ p)) (unit_positive p) budget obs
  have readOther := (sample_at (Γ := Δ) other f p s A B).eqSymm
  simp only [sample,otherClock] at readOther
  simpa only [diagonalEquivalent,subst_data,Syn.shift,Δ,s,A,B,p] using
    distance_congr (sample_at map f p s A B).eqSymm readOther
      (.eqRefl _) (.eqRefl _) near

theorem actual_named_right_half_plane_demand_frozen_rate_closed (map : RationalMap) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) (var 2) ⟶ le (clock map (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF map f) map.evaluator (data (var 0) (var 1) (var 2))
          (frozenData map f (var 4) (var 0) (var 1) (var 2)) one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (frozen_rate map f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneDemandComparison
