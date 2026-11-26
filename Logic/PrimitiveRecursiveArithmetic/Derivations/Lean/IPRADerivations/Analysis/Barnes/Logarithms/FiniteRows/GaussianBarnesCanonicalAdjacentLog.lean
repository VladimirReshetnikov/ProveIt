import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementLogGap
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperPowerCancellation
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# The adjacent Euler logarithm needed by the Barnes recurrence

The Barnes truncation at `N+1` matches the original Gamma Euler head
at `N`. The original named logarithm at these two cutoffs differs by
at most `1/N` in the independent observation metric.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalAdjacentLog

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev nameF : PR 2 := D logF logF
def data (N : PTm n) : PTm n := dd (succ N) N

theorem regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN nameF (data N) :=
  GaussianNamedDifference.name_regular _ _ _ _ (log_regular (succ N) (zero_lt_succ N)) (log_regular N hN)

theorem harmonic_log_cross (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent H logF (hd N one) N :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original N one (.andI hN (le_refl one))))
    (GaussianBetaUpperPowerCancellation.rational_log_integer N hN)

private theorem harmonic_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN H (hd N one) :=
  GaussianHarmonicLogarithmName.name_regular N one (.andI hN (le_refl one))

private theorem harmonic_observation (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (D H H) p (dd (hd (succ N) one) (hd N one))) (ap2 constantF p qzero)
      (unit p+num 6*N) (N*unit p) := by
  let a := ap2 H p (hd (succ N) one)
  let b := ap2 H p (hd N one)
  let x := ap2 (D H H) p (dd (hd (succ N) one) (hd N one))
  let U := unit p
  let E := N*U
  have hu := unit_positive (Γ := Γ) p
  have he := positive_product N U hN hu
  have hn : Γ ⊢[PRAAx] le two (succ N) := le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right one hN)
  have eq := pred_succ (Γ := Γ) N
  have gap : Γ ⊢[PRAAx] distanceBounded a b one N :=
    distance_congr (.eqRefl _) (congrAp2 H (.eqRefl _) (congrPairT eq (.eqRefl _))) (.eqRefl _) eq
      (GaussianStirlingGammaFractionalIncrementLogGap.log_gap (succ N) p hn)
  have raw : Γ ⊢[PRAAx] distanceBounded (qsub a b) qzero one N :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hN).iffMpr gap
  have rew := GaussianNamedDifference.sample_error H H (hd (succ N) one) (hd N one) p
    (harmonic_regular (succ N) (zero_lt_succ N)) (harmonic_regular N hN)
  have later := distance_radius_mono x (qsub a b) (num 6) U (num 6*N) E hu he
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [E]; ipra_ring)) rew
  have target := distance_radius_mono (qsub a b) qzero one N U E hN he
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [E]; ipra_ring)) raw
  exact distance_congr (.eqRefl _) (constant_at p qzero).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same x (qsub a b) qzero _ _ E he later target)

theorem rate (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data N) qzero one N := by
  let T := D H H
  let t := dd (hd (succ N) one) (hd N one)
  have a := harmonic_regular (Γ := Γ) (succ N) (zero_lt_succ N)
  have b := harmonic_regular (Γ := Γ) N hN
  have r : Γ ⊢[PRAAx] independentRate T constantF t qzero one N := by
    apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 6) hN
      (GaussianNamedDifference.name_regular _ _ _ _ a b) (constant_regular _)
    refine .allI ?_
    let Δ := Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift,Δ,one] using hN.shift
    have e := harmonic_observation (var 0) (Syn.shift N) hs
    have budget : Δ ⊢[PRAAx] (unit (var 0)+num 6*Syn.shift N) ≐ (one*unit (var 0)+num 6*Syn.shift N) := by
      ipra_ring
    simpa [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
      GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,T,t,Δ,one] using
        distance_congr (.eqRefl _) (.eqRefl _) budget (.eqRefl _) e
  have cross := GaussianNamedDifferenceQuotientProperness.difference_proper logF H logF H (succ N) (hd (succ N) one)
    N (hd N one) (log_regular _ (zero_lt_succ N)) a (log_regular _ hN) b
    (cross_symm _ _ _ _ (harmonic_log_cross (succ N) (zero_lt_succ N))) (cross_symm _ _ _ _ (harmonic_log_cross N hN))
  exact GaussianNamedRateTransport.transport T constantF nameF constantF t qzero (data N) qzero one N hN r
    cross (cross_refl _ _ (constant_regular _))

theorem actual_Barnes_adjacent_Gauss_logarithm_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ independentRate nameF constantF (data (var 0)) qzero one (var 0)) :=
  closeUniv 1 (.impI (rate _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalAdjacentLog
