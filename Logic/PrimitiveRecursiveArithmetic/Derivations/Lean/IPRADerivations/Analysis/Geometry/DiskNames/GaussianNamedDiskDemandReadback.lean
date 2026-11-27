import IPRADerivations.Analysis.Geometry.DiskNames.GaussianNamedDiskDemandLift
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Late rational readback of a named Gaussian disk map

Every native input observation past the finite demand clock gives an
independent rate to the lifted name by the same rational evaluator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedDiskDemandReadback

open_ipra
open GaussianNamedDiskDemandLift (RationalMap nameF clock sample_at frozenData clock_demand late_rate)
open GaussianBarnesCanonicalNamedDemand (source data)
open GaussianCoefficientNameBounds (unit)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedRateRadius (frozen_observation_of_rates)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem late_frozen_rate (map : RationalMap) (f : PR 2) (p s a k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock map s R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s)) :
    Γ ⊢[PRAAx] independentRate map.evaluator map.evaluator
      (frozenData map f (clock map p R) x R) (frozenData map f k x R) one (unit a) :=
  late_rate map f f a (clock map p R) k x x R hf hf (cross_refl _ _ hf.andE₁)
    (clock_demand map p R a hp) (le_trans (clock_demand map s R a hs) hk)

theorem frozen_observations (map : RationalMap) (f : PR 2) (p q s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock map s R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x R)) (ap2 map.evaluator q (frozenData map f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  have read := frozen_observation_of_rates map.evaluator map.evaluator p q s
    (frozenData map f (clock map p R) x R) (frozenData map f k x R)
    (late_frozen_rate map f p s (succ p) k x R hf.wk hk.wk (le_refl _) (Common.succ_le_succ Prf.hyp0))
    (late_frozen_rate map f p s s k x R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s))
  exact distance_congr (sample_at map f p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) read

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
