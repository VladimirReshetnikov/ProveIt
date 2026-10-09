import GowersSzemeredi.Proofs16RobustDifferenceBohr

/-!
SPDX-License-Identifier: Apache-2.0

Adapted for ProveIt from the progression extraction in openai/math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a, module
OAI/Combinatorics/Progressions/Estimates/LocalizedSiftingAlmostPeriods.lean.
The existing proper-progression theorem is applied to the robust event
controller, retaining uniformly many representations at every point.
See the adjacent LICENSE.openai-math for provenance and copyright terms.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def robustDifferenceProgressionConstant : Real := 11*(robustDifferenceBohrConstant+2)^2

theorem robustDifferenceProgressionConstant_pos : 0 < robustDifferenceProgressionConstant := by
  have h := robustDifferenceBohrConstant_pos
  unfold robustDifferenceProgressionConstant
  positivity

/-- Robust Bogolyubov progression extraction: every progression point
has at least `exp(-4p)N^3/8` four-term representations in the original set. -/
theorem exists_robust_difference_progression {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {p : Real} (hp : 0 ≤ p)
    (hA : Real.exp (-p)*N ≤ (A.card : Real)) :
    ∃ Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N,
      (Q.rank : Real) ≤ 2+robustDifferenceBohrConstant*(p+1)^4 ∧ Q.Proper ∧
      Real.exp (-(robustDifferenceProgressionConstant*(p+1)^8))*N ≤ (Q.carrier.card : Real) ∧
      ∀ t ∈ Q.carrier, (Real.exp (-p))^4/8*(N : Real)^3 ≤
        ((fourDifferenceRepresentations A t).card : Real) := by
  obtain ⟨R, hreg, hpos, hupper, hrank, hwidth, hcount⟩ := exists_robust_difference_bohr A hp hA
  obtain ⟨Q, hQrank, hproper, hQR, hmass⟩ :=
    OAI.Erdos3.BohrProgression.exists_proper_progression_of_quartic_bounds R
      robustDifferenceBohrConstant_pos.le hp hpos hupper hrank hwidth
  exact ⟨Q, hQrank, hproper, hmass, fun t ht => hcount t (hQR ht)⟩

end LeanProofs.GowersSzemeredi
