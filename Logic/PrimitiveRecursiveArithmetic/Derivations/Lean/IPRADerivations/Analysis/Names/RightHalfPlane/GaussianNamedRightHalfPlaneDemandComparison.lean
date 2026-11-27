import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneDemandLift
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

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
open GaussianNamedRateRadius (frozen_observation_of_rates)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem late_frozen_rate (map : RationalMap) (f : PR 2) (p s a k x M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s)) :
    Γ ⊢[PRAAx] independentRate map.evaluator map.evaluator
      (frozenData map f (clock map p M R) x M R) (frozenData map f k x M R) one (unit a) :=
  late_rate map f f a (clock map p M R) k x x M R hf hf (cross_refl _ _ hf.andE₁.andE₁)
    (clock_margin map p M R) (le_trans (clock_margin map s M R) hk)
    (clock_demand map p M R a hp) (le_trans (clock_demand map s M R a hs) hk)

theorem frozen_observations (map : RationalMap) (f : PR 2) (p q s k x M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x M R))
      (ap2 map.evaluator q (frozenData map f k x M R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  have read := frozen_observation_of_rates map.evaluator map.evaluator p q s
    (frozenData map f (clock map p M R) x M R) (frozenData map f k x M R)
    (late_frozen_rate map f p s (succ p) k x M R hf.wk hk.wk (le_refl _) (Common.succ_le_succ Prf.hyp0))
    (late_frozen_rate map f p s s k x M R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s))
  exact distance_congr (sample_at map f p x M R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) read

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
