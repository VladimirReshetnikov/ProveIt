import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7Named
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Freeze the original named reciprocal Gamma at an arbitrary late observation

The same exact modulus controls comparisons with the original rational
C7 evaluator, with separate observation clocks on the two sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaC7NamedFrozen

open_ipra
open GaussianGammaC7Named (nameF clock sample_at source data frozenData clock_demand late_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaC7Name (sample)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedRateRadius (frozen_observation_of_rates)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product ofGaussian)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (precision slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianGammaC7Name.nameF
local notation "D" => GaussianGammaC7Name.data
local notation "disk" => GaussianGammaCanonicalExponent.source

private theorem late_frozen_rate (f : PR 2) (p s a k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s)) :
    Γ ⊢[PRAAx] independentRate V V (frozenData f (clock p R) x R) (frozenData f k x R) one (unit a) :=
  late_rate f f a (clock p R) k x x R hf hf (cross_refl _ _ hf.andE₁.andE₁)
    (clock_demand p R a hp) (le_trans (clock_demand s R a hs) hk)

theorem frozen_observations (f : PR 2) (p q s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 V q (frozenData f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  have read := frozen_observation_of_rates V V p q s (frozenData f (clock p R) x R) (frozenData f k x R)
    (late_frozen_rate f p s (succ p) k x R hf.wk hk.wk (le_refl _) (Common.succ_le_succ Prf.hyp0))
    (late_frozen_rate f p s s k x R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s))
  exact distance_congr (sample_at f p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) read

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
