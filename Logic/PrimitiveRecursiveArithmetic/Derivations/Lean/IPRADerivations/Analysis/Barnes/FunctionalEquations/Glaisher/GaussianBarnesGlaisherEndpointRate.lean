import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherInterval

/-!
# Independent-clock endpoint rate for the actual Glaisher approximants

The finite inverse-square telescope is compared with independently chosen
observations of both original finite names. The remaining finite
observation cost is eliminated at an explicit integer-gap query.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherEndpointRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesGlaisherInterval (sample square square_positive)
open GaussianBarnesGlaisherFinite (nameF data regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack_removal_at precision)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem ordered_slack (p q t N r : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] distanceBounded (sample p (N+r)) (sample q N)
      (rateNumerator two (square N) p q*unit t + (two*r+two)*rateDenominator (square N) p q)
      (rateDenominator (square N) p q*unit t) := by
  let D := square N
  have h1 := le_trans (le_succ_self one) hN
  have hD := square_positive N h1
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hLeft := positive_product _ _ hp ht
  have hMid := positive_product _ _ hD ht
  have hRight := positive_product _ _ ht hq
  have hB := denominator_positive (square N) p q hD
  have left := GaussianNameEquivalence.point_at nameF (data (N+r)) p t
    (regular _ (le_trans h1 (le_add_right N r)))
  have mid := GaussianBarnesGlaisherInterval.uniform_interval t N r hN
  have right := GaussianNameEquivalence.point_at nameF (data N) t q (regular N h1)
  have leftMid := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hLeft hMid left mid
  have total := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (positive_product _ _ hLeft hMid) hRight leftMid right
  refine distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hLeft hMid) hRight) (positive_product _ _ hB ht) ?_ total
  apply le_of_eq_add (d := zero)
  unfold rateNumerator rateDenominator
  ipra_ring

theorem ordered_gap (p q N r : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] distanceBounded (sample p (N+r)) (sample q N)
      (rateNumerator two (square N) p q) (rateDenominator (square N) p q) := by
  let z := qsub (sample p (N+r)) (sample q N)
  let A := rateNumerator two (square N) p q
  let B := rateDenominator (square N) p q
  let C := two*r+two
  have hD := square_positive N (le_trans (le_succ_self one) hN)
  exact slack_removal_at z A B C (denominator_positive (square N) p q hD)
    (ordered_slack p q (precision z A B C) N r hN)

theorem independent_endpoint_rate (N r : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data (N+r)) (data N) two (square N) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] le two (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ,two,one] using hN.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,sample,data,square,sh,Δ,Syn.shift,GaussianBarnesGlaisherFinite.sumData,
    GaussianBarnesGlaisherFinite.weightedData,GaussianBarnesGlaisherFinite.squareQuarter,
    GaussianBarnesGlaisherQuartic.negativeWeight,GaussianBarnesGlaisherQuartic.weightNumerator,two,one]
    using ordered_gap (var 1) (var 0) (sh N) (sh r) hs

theorem actual_Glaisher_logarithm_independent_endpoint_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le two (var 0) ⟶ independentRate nameF nameF (data (var 0+var 1)) (data (var 0)) two (square (var 0))) :=
  closeUniv 2 (.impI (independent_endpoint_rate _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherEndpointRate
