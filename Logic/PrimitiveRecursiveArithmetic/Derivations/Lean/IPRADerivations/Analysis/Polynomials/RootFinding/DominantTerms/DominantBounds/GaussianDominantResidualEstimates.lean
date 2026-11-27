import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantDirectionData
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianBudgets.GaussianRationalThreeTermBudget
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianRationalDominantDecomposition

/-!
# Actual dominant-pair and residual decrease

The selected direction determines the actual displacement, main term,
direction error and other-term sum. Their individual relative squared
norm bounds are derived from the constructed direction and normalizer,
the exact pair identity, and the existing actual off-dominant sum bound.
The numerical three-weight budget then gives the exact source contraction.
Only the original balanced-radius input is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantResidualEstimates

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (input)
open LeanProofs.IPRA.Analysis.GaussianDominantDirectionData (base chosen precision direction P Q)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (winner)
open LeanProofs.IPRA.Analysis.GaussianOffDominantTerms (radiusNumerator radiusDenominator)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd qmul represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra (relative relative_congr relative_trans relative_scale)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianResidualDecreaseWeights (mainWeight errorWeight otherWeight)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (descentD)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def delta (C N : PTm n) : PTm n := GaussianDominantPairAlgebra.actualDelta
  (base C N) (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (winner C N)
def radial (C N : PTm n) : PTm n := GaussianDominantPairAlgebra.radialTerm
  (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (winner C N)
def main (C N : PTm n) : PTm n := GaussianDominantPairAlgebra.mainTerm
  (base C N) (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (winner C N) (precision C N)
def error (C N : PTm n) : PTm n := GaussianDominantPairAlgebra.errorTerm
  (base C N) (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (direction C N) (winner C N) (precision C N)
def other (C N : PTm n) : PTm n := GaussianOffDominantSum.otherSum C N (delta C N)
def scale (C N : PTm n) : PTm n := GaussianResidualDecreaseWeights.scale (GaussianDominantDirectionData.Q C N)

ipra_subst delta
ipra_subst radial
ipra_subst main
ipra_subst error
ipra_subst other
ipra_subst scale

theorem delta_inside (C N : PTm n) : Γ ⊢[PRAAx] GaussianOffDominantTerms.withinRadius C N (delta C N) :=
  GaussianDominantPairAlgebra.actual_within_radius _ _ _ _ _ (GaussianDominantDirectionData.denominator_positive C N)

theorem radial_reference (C N : PTm n) : Γ ⊢[PRAAx] radial C N ≐ GaussianOffDominantTerms.selectedReference C N := by
  have hD := positive_product (Γ := Γ) _ _ (GaussianRationalL1.raw_den_positive (chosen C N))
    (RationalNonnegativePowers.denominator_positive (radiusDenominator C N) (winner C N)
      (GaussianDominantDirectionData.denominator_positive C N))
  exact GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hD) hD
    (GaussianDominantPairAlgebra.radial_represents _ _ _ _ (GaussianDominantDirectionData.denominator_positive C N))
    (GaussianRationalHorner.ofGaussian_represents _ _ hD)

theorem radial_norm (C N : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (radial C N) ≐ GaussianOffDominantSum.selectedScore C N :=
  (GaussianRationalProductWitness.qnormSq_congr (radial_reference C N)).eqTrans
    (GaussianOffDominantTerms.selected_reference_norm C N)

theorem radial_bound (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    relative (radial C N) (GaussianRationalDirectionNormalizer.sixtyFive*P C N)
      (GaussianRationalDirectionNormalizer.sixtyFour*GaussianDominantDirectionData.Q C N) (base C N) :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_congr (.eqRefl _) (radial_norm C N).eqSymm)
    (.eqRefl _) (GaussianDominantDirectionData.radial_relative C N h)

theorem main_bound (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    relative (main C N) (mainWeight (P C N) (GaussianDominantDirectionData.Q C N)) (scale C N) (base C N) :=
  relative_scale _ _ _ _ (num 6144)
    (GaussianRationalRelativeNormAlgebra.scaled_point_relative (monus (GaussianDominantDirectionData.Q C N) (P C N)) (GaussianDominantDirectionData.Q C N) (base C N)
      (GaussianDominantDirectionData.alpha_denominator_positive C N h))

theorem phase_error_bound (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (power (direction C N) (winner C N))
      (GaussianDominantDirectionData.target C N) one (num 32) :=
  GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (le_of_eq_add (d := one+two) (by unfold GaussianDominantSyntax.four; ipra_ring))
      (le_of_eq_add (d := num 15) (by ipra_ring)))
    (le_of_eq_add (d := num 31) (by ipra_ring))
    (le_of_eq_add (d := num 32) (by unfold GaussianDominantSyntax.four; ipra_ring))
    (GaussianDominantDirectionData.direction_error C N h)

theorem error_bound (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    relative (error C N) (errorWeight (P C N)) (scale C N) (base C N) := by
  have first : Γ ⊢[PRAAx] relative (error C N) one (num 32) (radial C N) :=
    GaussianRationalRelativeNormAlgebra.product_relative _ _ one (num 32)
      (le_of_eq_add (d := num 31) (by ipra_ring)) (phase_error_bound C N h)
  have combined := relative_trans _ _ _ _ _ _ _ first (radial_bound C N h)
  have scaled := relative_scale _ _ _ _ (num 3) combined
  exact relative_congr (.eqRefl _)
    (by unfold errorWeight GaussianRationalDirectionNormalizer.sixtyFive GaussianRationalDirectionNormalizer.sixtyFour; ipra_ring)
    (by unfold scale GaussianResidualDecreaseWeights.scale GaussianRationalDirectionNormalizer.sixtyFour; ipra_ring)
    (.eqRefl _) scaled

theorem other_relative_radial (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    relative (other C N) (num 2) (num 3) (radial C N) :=
  RationalArgmin.rationalLE_congr
    (GaussianRationalRelativeNormAlgebra.weighted_congr (.eqRefl _)
      (by unfold GaussianRationalNormClearing.nine GaussianRationalNormClearing.three; ipra_ring))
    (RationalAlgebra.multiply_congr
      (RationalNonnegativePowers.fraction_congr (by unfold GaussianDominantSyntax.four; ipra_ring) (.eqRefl _))
      (radial_norm C N).eqSymm)
    (GaussianOffDominantSum.off_dominant_sum C N (delta C N) h (delta_inside C N))

theorem other_bound (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    relative (other C N) (otherWeight (P C N)) (scale C N) (base C N) := by
  have combined := relative_trans _ _ _ _ _ _ _ (other_relative_radial C N h) (radial_bound C N h)
  exact relative_congr (.eqRefl _)
    (by unfold otherWeight GaussianRationalDirectionNormalizer.sixtyFive GaussianRationalDirectionNormalizer.sixtyFour; ipra_ring)
    (by unfold scale GaussianResidualDecreaseWeights.scale GaussianRationalDirectionNormalizer.sixtyFour; ipra_ring)
    (.eqRefl _) (relative_scale _ _ _ _ (num 32) combined)

theorem evaluation_decomposition (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate C (delta C N) ≐ GaussianRationalThreeTermBudget.sum (main C N) (error C N) (other C N) :=
  (GaussianRationalDominantDecomposition.dominant_decomposition C N (delta C N) (winner C N) (Prf.andE₁ h)
    (Prf.andE₁ (GaussianDominantPlateau.winner_bounds C N h)) (Prf.andE₂ (GaussianDominantPlateau.winner_bounds C N h))).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr
      (GaussianDominantPairAlgebra.actual_pair_decomposition _ _ _ _ _ (GaussianDominantDirectionData.denominator_positive C N)
        (GaussianDominantDirectionData.alpha_le_one C N h)) (.eqRefl _))

/-- All individual estimates and alpha/clock guards are produced from
the actual selected data of the original coefficient list. -/
theorem residual_decrease (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (GaussianRationalHorner.evaluate C (delta C N)))
      (RationalArithmetic.multiply
        (GaussianRationalMetric.squaredTolerance (GaussianResidualDecreaseWeights.rateNum (descentD N))
          (GaussianResidualDecreaseWeights.rateDen (descentD N))) (GaussianRationalMetric.qnormSq (base C N))) := by
  have actual := GaussianRationalThreeTermBudget.from_alpha (main C N) (error C N) (other C N) (base C N)
    (descentD N) (P C N) (GaussianDominantDirectionData.Q C N) (GaussianDominantDirectionData.clock_positive N)
    (GaussianDominantDirectionData.alpha_denominator_positive C N h) (GaussianDominantDirectionData.alpha_le_one C N h)
    (GaussianDominantDirectionData.alpha_lower_bound C N h) (main_bound C N h) (error_bound C N h) (other_bound C N h)
  exact RationalArgmin.rationalLE_congr
    (GaussianRationalProductWitness.qnormSq_congr (evaluation_decomposition C N h)).eqSymm (.eqRefl _) actual

def contraction (C N : PTm n) : Fm PTm n := RationalArgmin.rationalLE
  (GaussianRationalMetric.qnormSq (GaussianRationalHorner.evaluate C (delta C N)))
  (RationalArithmetic.multiply
    (GaussianRationalMetric.squaredTolerance (GaussianResidualDecreaseWeights.rateNum (descentD N))
      (GaussianResidualDecreaseWeights.rateDen (descentD N))) (GaussianRationalMetric.qnormSq (base C N)))
ipra_subst contraction

def output (C N : PTm n) : PTm n := pairT (delta C N) (pairT (GaussianRationalHorner.evaluate C (delta C N))
  (pairT (main C N) (pairT (error C N) (pairT (other C N) (GaussianDominantDirectionData.run C N)))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N

ipra_subst output
ipra_subst run
theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_delta (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ delta C N :=
  (program_at C N).fstE

theorem returned_value (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ GaussianRationalHorner.evaluate C (delta C N) :=
  (program_at C N).sndE.fstE

theorem returned_main (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N))) ≐ main C N :=
  (program_at C N).sndE.sndE.fstE

theorem returned_error (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N)))) ≐ error C N :=
  (program_at C N).sndE.sndE.sndE.fstE

theorem returned_other (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run C N))))) ≐ other C N :=
  (program_at C N).sndE.sndE.sndE.sndE.fstE

theorem returned_data (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run C N))))) ≐ GaussianDominantDirectionData.run C N :=
  (program_at C N).sndE.sndE.sndE.sndE.sndE

theorem actual_residual_decrease_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ contraction (var 0) (var 1)) :=
  closeUniv 2 (.impI (residual_decrease _ _ Prf.hyp0))

theorem actual_residual_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ GaussianRationalHorner.evaluate (var 0) (delta (var 0) (var 1)) ≐
      GaussianRationalThreeTermBudget.sum (main (var 0) (var 1)) (error (var 0) (var 1)) (other (var 0) (var 1))) :=
  closeUniv 2 (.impI (evaluation_decomposition _ _ Prf.hyp0))

theorem actual_delta_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianOffDominantTerms.withinRadius (var 0) (var 1) (delta (var 0) (var 1))) := closeUniv 2 (delta_inside _ _)

theorem actual_residual_trace_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Analysis.GaussianDominantResidualEstimates
