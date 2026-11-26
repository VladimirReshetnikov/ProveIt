import IPRADerivations.Analysis.Geometry.DiskNames.GaussianNamedDiskDemandLift

/-!
# Late rational readback of a named Gaussian disk map

Every native input observation past the finite demand clock gives an
independent rate to the lifted name by the same rational evaluator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedDiskDemandReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDiskDemandLift (RationalMap nameF clock sample_at frozenData clock_demand late_rate)
open GaussianBarnesCanonicalNamedDemand (source data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

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
    exact le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (W*S*P*Q*(two*P+Q)) (mul_le_mul_right (P*Q*Q) h))
  have double : Γ ⊢[PRAAx] unit (succ p) ≐ two*P := (pw_succ two p).eqTrans (mul_comm _ _)
  exact le_congr
    (congrMul (congrAdd (congrMul (congrMul (.eqRefl _) double) (.eqRefl _))
      (congrMul (.eqRefl _) (congrAdd double (.eqRefl _)))) (.eqRefl _)).eqSymm
    (congrMul (.eqRefl _) (congrMul (congrMul (.eqRefl _) double) (.eqRefl _))).eqSymm cleared

private theorem read_with (map : RationalMap) (f : PR 2) (p q s a k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock map s R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s))
    (hb : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x R)) (ap2 map.evaluator q (frozenData map f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let r := clock map p R
  have rate := late_rate map f f a r k x x R hf hf (cross_refl _ _ hf.andE₁)
    (clock_demand map p R a hp) (le_trans (clock_demand map s R a hs) hk)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive a))
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget p q s a hb)
    (rate_at _ _ _ _ _ _ (succ p) q rate)
  exact distance_congr (sample_at map f p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_observations (map : RationalMap) (f : PR 2) (p q s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock map s R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x R)) (ap2 map.evaluator q (frozenData map f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  refine .orE (le_total p s) ?_ ?_
  · have lp : le p s :: Γ ⊢[PRAAx] le (succ p) (succ s) :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one Prf.hyp0)
    have double : le p s :: Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
    have hb : le p s :: Γ ⊢[PRAAx] le (two*unit p*unit s) ((two*unit p)*(two*unit p+unit s)) :=
      le_of_eq_add (d := two*unit p*(two*unit p)) (by ipra_ring)
    exact read_with map f p q s (succ p) k x R hf.wk hk.wk (le_refl _) lp
      (le_congr (.eqRefl _) (congrMul double.eqSymm (.eqRefl _)) hb)
  · have hb : le s p :: Γ ⊢[PRAAx] le (two*unit p*unit s) (unit s*(two*unit p+unit s)) :=
      le_of_eq_add (d := unit s*unit s) (by ipra_ring)
    exact read_with map f p q s s k x R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s) hb

theorem frozen_rate (map : RationalMap) (f : PR 2) (s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock map s R) k) :
    Γ ⊢[PRAAx] independentRate (nameF map f) map.evaluator (data x R) (frozenData map f k x R) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have later : Δ ⊢[PRAAx] le (clock map (sh s) (sh R)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate,GaussianBarnesCanonicalNamedDemand.subst_data,GaussianNamedDiskDemandLift.subst_frozenData,
    GaussianCoefficientNameBounds.subst_unit,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
      frozen_observations map f (var 1) (var 0) (sh s) (sh k) (sh x) (sh R) h later

end LeanProofs.IPRA.Analysis.GaussianNamedDiskDemandReadback
