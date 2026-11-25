import IPRADerivations.Analysis.GaussianGammaNegativeIntervalCriticalDerivativeZero

/-!
# Independent derivative observations at the negative critical grid point

The certified small observation at the selected rational is a single
anchor for that original derivative target. Its Cauchy bound transports
the comparison to an arbitrary observation of the derivative and an
independent observation of the constant zero name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalResidualRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeCriticalLocation (lower_guard)
open GaussianGammaNegativeIntervalCriticalDerivativeZero
  (argumentNumerator argumentDenominator evaluationClock locationClock quotientClock target_small)
open GaussianGammaNegativeIntervalCriticalQuotientZero (stage)
open GaussianGammaNegativeIntervalDerivativeTarget (target_regular)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (zeroF zero_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "TF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "TD" => GaussianGammaNegativeIntervalDerivativeTarget.data

private theorem observation_bound (f : PR 2) (x t D p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] le D (unit t))
    (hs : Γ ⊢[PRAAx] distanceBounded (ap2 f t x) qzero one D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 zeroF q qzero)
      (rateNumerator two D p q) (rateDenominator D p q) := by
  let P := unit p
  let Q := unit q
  let T := unit t
  have hPT : Γ ⊢[PRAAx] le one (P*T) := positive_product _ _ (unit_positive p) (unit_positive t)
  have ineq := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hPT hD (point_at f x p t hf) hs
  apply distance_congr (.eqRefl _) (zero_at q qzero).eqSymm (.eqRefl _) (.eqRefl _)
  refine distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hPT hD) (denominator_positive D p q hD) ?_ ineq
  change Γ ⊢[PRAAx] le (((P+T)*D+one*(P*T))*(D*P*Q))
    ((two*P*Q+D*(P+Q))*((P*T)*D))
  ipra_le 𝔞(D*P*P*Q)*sl ht+𝔞(D*D*P*P*T) using dsimp only [P,Q,T]; ring

private theorem independent_of_observation (f : PR 2) (x t D : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] le D (unit t))
    (hs : Γ ⊢[PRAAx] distanceBounded (ap2 f t x) qzero one D) :
    Γ ⊢[PRAAx] independentRate f zeroF x qzero two D := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hfs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift.shift
  have hDs : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have hts : Δ ⊢[PRAAx] le (sh D) (unit (sh t)) := by simpa [Δ,Fm.shift,Syn.shift,sh] using ht.shift.shift
  have hss : Δ ⊢[PRAAx] distanceBounded (ap2 f (sh t) (sh x)) qzero one (sh D) := by
    simpa [Δ,Fm.shift,Syn.shift,sh,one] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,sh,Syn.shift,GaussianRationalHorner.subst_qzero,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observation_bound f (sh x) (sh t) (sh D) (var 1) (var 0) hfs hDs hts hss

theorem original_rate (p N : PTm n) : Γ ⊢[PRAAx]
    independentRate TF zeroF (TD (argumentNumerator p N) (argumentDenominator p N) N) qzero two (unit (stage p)) := by
  have selected := lower_guard (Γ := Γ) (locationClock p N) N
  have time : Γ ⊢[PRAAx] le (stage p) (quotientClock p N) :=
    le_trans (le_add_right (stage p) _) (le_succ_self (evaluationClock p N))
  exact independent_of_observation TF _ (quotientClock p N) (unit (stage p)) (target_regular _ _ _ selected)
    (unit_positive (stage p)) (GaussianExponentialReference.unit_monotone time) (target_small p N)

theorem actual_original_negative_Gamma_critical_residual_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (independentRate TF zeroF (TD (argumentNumerator (var 0) (var 1)) (argumentDenominator (var 0) (var 1)) (var 1))
        qzero two (unit (stage (var 0)))) :=
  closeUniv 2 (original_rate _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalResidualRate
