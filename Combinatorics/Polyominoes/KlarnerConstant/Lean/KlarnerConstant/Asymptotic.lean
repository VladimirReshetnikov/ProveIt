import KlarnerConstant.Growth
import Mathlib.Analysis.Subadditive

/-!
# Fekete's lemma and the conventional nth-root growth constant

`Growth.lean` defines `growthSup A` as the supremum of all positive-index
real nth roots of `A`.  This module proves that, for a positive
supermultiplicative sequence with an exponential majorant, the conventional
nth-root sequence converges and its limit is exactly that supremum.

Only positive indices matter.  To use mathlib's additive form of Fekete's
lemma without imposing an artificial condition on `A 0`, `feketeNegLog A 0`
is defined to be zero and its positive-index values are `-log (A n)`.
-/

namespace LeanProofs.KlarnerConstant

open Filter Set Topology

/-- The conventional real nth root of an integer-valued sequence.  Its value
at index zero is harmless because convergence is taken along `atTop`. -/
noncomputable def realNthRoot (A : ℕ → ℕ) (n : ℕ) : ℝ :=
  (A n : ℝ) ^ (n⁻¹ : ℝ)

/-- Positivity at every index which participates in an nth root. -/
def PositiveOnPositiveIndices (A : ℕ → ℕ) : Prop :=
  ∀ n, n ≠ 0 → 0 < A n

/-- Supermultiplicativity restricted to positive indices.  This avoids any
convention about whether the combinatorial empty object is counted by `A 0`.
-/
def SupermultiplicativeOnPositive (A : ℕ → ℕ) : Prop :=
  ∀ m n, m ≠ 0 → n ≠ 0 → A m * A n ≤ A (m + n)

/-- The subadditive sequence to which Fekete's lemma is applied. -/
noncomputable def feketeNegLog (A : ℕ → ℕ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else -Real.log (A n : ℝ)

/-- The negative logarithms of a positive supermultiplicative sequence form a
subadditive sequence. -/
theorem feketeNegLog_subadditive {A : ℕ → ℕ}
    (hpos : PositiveOnPositiveIndices A)
    (hsuper : SupermultiplicativeOnPositive A) :
    Subadditive (feketeNegLog A) := by
  intro m n
  by_cases hm : m = 0
  · subst m
    simp [feketeNegLog]
  by_cases hn : n = 0
  · subst n
    simp [feketeNegLog]
  have hmn : m + n ≠ 0 := by omega
  have hmpos : 0 < (A m : ℝ) := by
    exact_mod_cast hpos m hm
  have hnpos : 0 < (A n : ℝ) := by
    exact_mod_cast hpos n hn
  have hmul :
      (A m : ℝ) * (A n : ℝ) ≤ (A (m + n) : ℝ) := by
    exact_mod_cast hsuper m n hm hn
  have hlog := Real.log_le_log (mul_pos hmpos hnpos) hmul
  rw [Real.log_mul hmpos.ne' hnpos.ne'] at hlog
  simp only [feketeNegLog, if_neg hm, if_neg hn, if_neg hmn]
  linarith

/-- An exponential majorant bounds the Fekete logarithmic slopes below. -/
theorem feketeNegLog_div_bddBelow {A : ℕ → ℕ} {μ : ℝ}
    (hpos : PositiveOnPositiveIndices A) (hμ : 1 ≤ μ)
    (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) :
    BddBelow (range fun n : ℕ ↦ feketeNegLog A n / (n : ℝ)) := by
  refine ⟨-Real.log μ, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simpa [feketeNegLog] using neg_nonpos.mpr (Real.log_nonneg hμ)
  have hnpos : 0 < (A n : ℝ) := by
    exact_mod_cast hpos n hn
  have hlog : Real.log (A n : ℝ) ≤ Real.log (μ ^ n) :=
    Real.log_le_log hnpos (hmajor n)
  rw [Real.log_pow] at hlog
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [feketeNegLog, if_neg hn]
  rw [le_div_iff₀ hnreal]
  calc
    -Real.log μ * (n : ℝ) = -((n : ℝ) * Real.log μ) := by ring
    _ ≤ -Real.log (A n : ℝ) := neg_le_neg hlog

/-- The nth root is the exponential of the negated Fekete logarithmic slope.
This identity also holds at index zero. -/
theorem realNthRoot_eq_exp_neg_feketeNegLog {A : ℕ → ℕ}
    (hpos : PositiveOnPositiveIndices A) (n : ℕ) :
    realNthRoot A n =
      Real.exp (-(feketeNegLog A n / (n : ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp [realNthRoot, feketeNegLog]
  have hnpos : 0 < (A n : ℝ) := by
    exact_mod_cast hpos n hn
  rw [realNthRoot, Real.rpow_def_of_pos hnpos]
  congr 1
  simp only [feketeNegLog, if_neg hn, div_eq_mul_inv]
  ring

/-- A pointwise exponential majorant makes `rootSet A` bounded above. -/
theorem rootSet_bddAbove_of_le_pow {A : ℕ → ℕ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) :
    BddAbove (rootSet A) := by
  refine ⟨μ, ?_⟩
  rintro x ⟨n, hn, rfl⟩
  exact root_le_of_le_pow hμ hmajor hn

/-- Under a pointwise exponential majorant, every positive-index nth root is
at most `growthSup A`. -/
theorem realNthRoot_le_growthSup {A : ℕ → ℕ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n)
    {n : ℕ} (hn : n ≠ 0) : realNthRoot A n ≤ growthSup A := by
  apply le_csSup (rootSet_bddAbove_of_le_pow hμ hmajor)
  exact ⟨n, hn, rfl⟩

/-- Fekete's lemma gives convergence of the nth-root sequence to the
exponential of the limiting logarithmic slope. -/
theorem tendsto_realNthRoot_feketeLimit {A : ℕ → ℕ} {μ : ℝ}
    (hpos : PositiveOnPositiveIndices A)
    (hsuper : SupermultiplicativeOnPositive A) (hμ : 1 ≤ μ)
    (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) :
    Tendsto (realNthRoot A) atTop
      (𝓝 (Real.exp
        (-(feketeNegLog_subadditive hpos hsuper).lim))) := by
  have hslopes :=
    (feketeNegLog_subadditive hpos hsuper).tendsto_lim
      (feketeNegLog_div_bddBelow hpos hμ hmajor)
  have hexp :
      Tendsto
        (fun n : ℕ ↦ Real.exp (-(feketeNegLog A n / (n : ℝ))))
        atTop
        (𝓝 (Real.exp
          (-(feketeNegLog_subadditive hpos hsuper).lim))) := by
    simpa only [Function.comp_def] using
      (Real.continuous_exp.tendsto
        (-(feketeNegLog_subadditive hpos hsuper).lim)).comp hslopes.neg
  have heq : realNthRoot A =
      fun n : ℕ ↦ Real.exp (-(feketeNegLog A n / (n : ℝ))) := by
    funext n
    exact realNthRoot_eq_exp_neg_feketeNegLog hpos n
  rw [heq]
  exact hexp

/-- Every positive-index nth root lies below the Fekete limit. -/
theorem realNthRoot_le_feketeLimit {A : ℕ → ℕ} {μ : ℝ}
    (hpos : PositiveOnPositiveIndices A)
    (hsuper : SupermultiplicativeOnPositive A) (hμ : 1 ≤ μ)
    (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n)
    {n : ℕ} (hn : n ≠ 0) :
    realNthRoot A n ≤
      Real.exp (-(feketeNegLog_subadditive hpos hsuper).lim) := by
  rw [realNthRoot_eq_exp_neg_feketeNegLog hpos]
  apply Real.exp_le_exp.mpr
  exact neg_le_neg
    ((feketeNegLog_subadditive hpos hsuper).lim_le_div
      (feketeNegLog_div_bddBelow hpos hμ hmajor) hn)

/-- The supremal definition of growth is exactly the Fekete nth-root limit. -/
theorem growthSup_eq_exp_neg_feketeLim {A : ℕ → ℕ} {μ : ℝ}
    (hpos : PositiveOnPositiveIndices A)
    (hsuper : SupermultiplicativeOnPositive A) (hμ : 1 ≤ μ)
    (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) :
    growthSup A =
      Real.exp (-(feketeNegLog_subadditive hpos hsuper).lim) := by
  apply le_antisymm
  · apply csSup_le (rootSet_nonempty A)
    rintro x ⟨n, hn, rfl⟩
    exact realNthRoot_le_feketeLimit hpos hsuper hμ hmajor hn
  · have hlim := tendsto_realNthRoot_feketeLimit hpos hsuper hμ hmajor
    apply le_of_tendsto hlim
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact realNthRoot_le_growthSup (zero_le_one.trans hμ) hmajor
      (Nat.ne_of_gt (zero_lt_one.trans_le hn))

/-- Conventional formulation: the positive real nth roots converge to
`growthSup A`. -/
theorem tendsto_realNthRoot_growthSup {A : ℕ → ℕ} {μ : ℝ}
    (hpos : PositiveOnPositiveIndices A)
    (hsuper : SupermultiplicativeOnPositive A) (hμ : 1 ≤ μ)
    (hmajor : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) :
    Tendsto (realNthRoot A) atTop (𝓝 (growthSup A)) := by
  rw [growthSup_eq_exp_neg_feketeLim hpos hsuper hμ hmajor]
  exact tendsto_realNthRoot_feketeLimit hpos hsuper hμ hmajor

end LeanProofs.KlarnerConstant
