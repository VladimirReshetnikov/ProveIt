import GowersSzemeredi.Proofs18GeneralIteration
import GowersSzemeredi.Sections17_18

/-! The exact quantitative theorem follows from an explicit function
inverse theorem whose constants fit the proved iteration threshold.
This reduction keeps both outstanding requirements visible. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The remaining quantitative input: a function discrepancy bound at the
relative counting parameter, with its entire iteration threshold below
the source's claimed threshold. This proposition is not asserted. -/
def Section18DiscrepancyBudget : Prop :=
  ∀ (delta : Real) (k : Nat), 0 < delta → delta ≤ 1 / 2 → 2 ≤ k →
    ∃ beta sigma T : Real, 0 < beta ∧ 0 < sigma ∧
      FunctionDiscrepancyBound (k - 2) (intervalUniformityParameter delta k) beta sigma T ∧
      intervalDiscrepancyClosedThreshold k delta beta sigma T ≤ szemerediThreshold delta k

/-- Complete the exact natural-interval formulation of Theorem 18.2 from
the explicit discrepancy budget. The length-one case is handled directly. -/
theorem theorem_18_2_of_function_discrepancy_budget
    (hbudget : Section18DiscrepancyBudget) : theorem_18_2 := by
  intro delta k N hδ hδhalf hk hN A hA hcard
  by_cases hkone : k = 1
  · subst k
    have hthreshold : 0 < szemerediThreshold delta 1 := by
      unfold szemerediThreshold
      positivity
    have hNpos : (0 : Real) < N := hthreshold.trans_le hN
    have hApos : (0 : Real) < A.card := (mul_pos hδ hNpos).trans_le hcard
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by exact_mod_cast hApos)
    refine ⟨a, 1, by omega, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    simpa only [hi0, Nat.zero_mul, Nat.add_zero] using ha
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨beta, sigma, T, hβ, hσ, hbound, hsize⟩ := hbudget delta k hδ hδhalf hk2
    exact hbound.natural_szemeredi_closed hk2 hδ hβ hσ N (hsize.trans hN) A hA hcard

end LeanProofs.GowersSzemeredi
