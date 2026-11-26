import IPRADerivations.Analysis.GaussianGammaC7Named
import IPRADerivations.Analysis.GaussianRationalPowerDifference

/-!
# Freeze the original named reciprocal Gamma at an arbitrary late observation

The same exact modulus controls comparisons with the original rational
C7 evaluator, with separate observation clocks on the two sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaC7NamedFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaC7Named (nameF clock sample_at source data frozenData clock_demand late_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaC7Name (sample)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product ofGaussian)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (precision slack_removal_at)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianGammaC7Name.nameF
local notation "D" => GaussianGammaC7Name.data
local notation "disk" => GaussianGammaCanonicalExponent.source

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

private theorem read_with (f : PR 2) (p q s a k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s))
    (hb : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 V q (frozenData f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let r := clock p R
  have rate := late_rate f f a r k x x R hf hf (cross_refl _ _ hf.andE₁.andE₁)
    (clock_demand p R a hp) (le_trans (clock_demand s R a hs) hk)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive a))
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget p q s a hb)
    (rate_at _ _ _ _ _ _ (succ p) q rate)
  exact distance_congr (sample_at f p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_observations (f : PR 2) (p q s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 V q (frozenData f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  refine .orE (le_total p s) ?_ ?_
  · have lp : le p s :: Γ ⊢[PRAAx] le (succ p) (succ s) :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one Prf.hyp0)
    have double : le p s :: Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
    have hb : le p s :: Γ ⊢[PRAAx] le (two*unit p*unit s) ((two*unit p)*(two*unit p+unit s)) :=
      le_of_eq_add (d := two*unit p*(two*unit p)) (by ipra_ring)
    exact read_with f p q s (succ p) k x R hf.wk hk.wk (le_refl _) lp
      (le_congr (.eqRefl _) (congrMul double.eqSymm (.eqRefl _)) hb)
  · have hb : le s p :: Γ ⊢[PRAAx] le (two*unit p*unit s) (unit s*(two*unit p+unit s)) :=
      le_of_eq_add (d := unit s*unit s) (by ipra_ring)
    exact read_with f p q s s k x R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s) hb

theorem frozen_rate (f : PR 2) (s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) V (data x R) (frozenData f k x R) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have later : Δ ⊢[PRAAx] le (clock (sh s) (sh R)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate,GaussianGammaC7Named.subst_data,GaussianGammaC7Named.subst_frozenData,
    GaussianCoefficientNameBounds.subst_unit,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
      frozen_observations f (var 1) (var 0) (sh s) (sh k) (sh x) (sh R) h later

private theorem chart_observations (z w R B E p q : PTm n)
    (hz : Γ ⊢[PRAAx] disk z R B) (hw : Γ ⊢[PRAAx] disk w R E) (h : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w E) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (sample q w R E) (unit p+unit q) (unit p*unit q) := by
  apply slack_removal_at _ _ _ one (positive_product _ _ (unit_positive p) (unit_positive q))
  let s := precision (qsub (sample p z R B) (sample q w R E)) (unit p+unit q) (unit p*unit q) one
  let U := unit (GaussianGammaInputContinuity.modulus s R)
  have close := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ofGaussian z B) U (unit_positive _)
  have fine := distance_radius_mono _ _ _ _ one U (unit_positive _) (unit_positive _)
    (le_congr (by ipra_ring) (.eqRefl _) (zero_le _)) close
  have rate := GaussianGammaHalfPlaneInputContinuity.original_C7_mixed_rate s z w R B E hz hw
    (distance_congr (.eqRefl _) h (.eqRefl _) (.eqRefl _) fine)
  change Γ ⊢[PRAAx] distanceBounded (sample p z R B) (sample q w R E)
    ((unit p+unit q)*unit s+one*(unit p*unit q)) ((unit p*unit q)*unit s)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) (rate_at _ _ _ _ _ _ p q rate)

theorem chart_cross (z w R B E : PTm n)
    (hz : Γ ⊢[PRAAx] disk z R B) (hw : Γ ⊢[PRAAx] disk w R E) (h : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w E) :
    Γ ⊢[PRAAx] crossEquivalent V V (D z R B) (D w R E) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have zr : Δ ⊢[PRAAx] disk (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  have wr : Δ ⊢[PRAAx] disk (sh w) (sh R) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hw.shift.shift
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh E) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  simpa only [crossEquivalent,GaussianGammaC7Name.sample,GaussianGammaC7Name.subst_data,Syn.shift,sh,Δ] using
    chart_observations (sh z) (sh w) (sh R) (sh B) (sh E) (var 1) (var 0) zr wr eq

theorem actual_original_C7_named_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 1) ⟶ le (clock (var 2) (var 1)) (var 3) ⟶
        independentRate (nameF f) V (data (var 0) (var 1)) (frozenData f (var 3) (var 0) (var 1))
          one (unit (var 2))) :=
  closeUniv 4 (.impI (.impI (frozen_rate f _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaC7NamedFrozen
