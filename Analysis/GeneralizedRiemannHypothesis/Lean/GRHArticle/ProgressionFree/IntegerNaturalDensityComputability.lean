import GRHArticle.ProgressionFree.IntegerFiniteTemplateOptimization
import Mathlib.Data.Nat.Find

/-!
# Computability of the extremal integer natural densities

The program tests only rational inequalities. It selects the smooth primes
by the requested precision, searches for a sufficient truncation, and
solves the finite weighted maximization at that cutoff.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

private theorem exists_integerTemplateCutoff (Y k : ℕ) :
    ∃ H, integerTemplateTruncationError Y H ≤ (1/2:ℚ)^(k+1) := by
  have h := (tendsto_integerTemplateTruncationError Y).eventually_lt_const
    (by positivity : (0:ℝ) < (1/2:ℝ)^(k+1))
  obtain ⟨H,hH⟩ := h.exists
  refine ⟨H,(Rat.cast_le (K := ℝ)).mp ?_⟩
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hH.le

/-- A computable cutoff for the total reciprocal weight missed by the finite template. -/
def integerTemplateCutoff (Y k : ℕ) : ℕ := Nat.find (exists_integerTemplateCutoff Y k)

theorem integerTemplateCutoff_spec (Y k : ℕ) :
    integerTemplateTruncationError Y (integerTemplateCutoff Y k) ≤ (1/2:ℚ)^(k+1) :=
  Nat.find_spec (exists_integerTemplateCutoff Y k)

/-- Rational approximation to the extremal natural density with dyadic precision. -/
def integerNaturalDensityApprox (integral : Bool) (k : ℕ) : ℚ :=
  let Y := 2^(k+1)
  integerFiniteTemplateApprox integral Y (integerTemplateCutoff Y k)

/-- The program approximates the supremum over all admissible sets, for
either ratio convention, with error at most `2^(-(k+1))`. -/
theorem integerNaturalDensityApprox_error (integral : Bool) (k : ℕ) :
    |(integerNaturalDensityApprox integral k : ℝ) - integerNaturalDensitySupremum integral| ≤
      (1/2:ℝ)^(k+1) := by
  let Y : ℕ := 2^(k+1)
  let H := integerTemplateCutoff Y k
  have ht : integerTemplateTruncationError Y H ≤ (1/2:ℚ)^(k+1) := integerTemplateCutoff_spec Y k
  have hreal := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hreal
  obtain ⟨ha,hb⟩ := integerFiniteTemplateApprox_bounds integral Y H
  obtain ⟨hc,hd⟩ := integerSmoothLowerOptimization_error integral Y
  have he := integerPrimeSquareTail_le_reciprocal (Y := Y) (by dsimp [Y]; positivity)
  have hdy : 1/(Y:ℝ) = (1/2:ℝ)^(k+1) := by simp [Y]
  rw [hdy] at he
  change |(integerFiniteTemplateApprox integral Y H : ℝ) - _| ≤ _
  apply abs_le.mpr
  constructor <;> linarith only [ha,hb,hc,hd,he,hreal]

end GRHArticle.ProgressionFree
