import GRHArticle.ProgressionFree.PolynomialIrreducibleDegrees
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Real.Sqrt

/-!
# Integer moment budgets for the 74-deficit search

For the five numerical cutoffs it suffices to use the degree bound
`d I_q(d) ≤ q^d` in each upward-rounded summand. The resulting integers
bound the article's cutoffs without enumerating polynomials over a field.
-/

namespace GRHArticle.ProgressionFree

/-- Upward-rounded contribution to the mean for the total prime degree `m = d I_q(d)`. -/
def polynomialMeanCeilTerm (d m : ℕ) : ℕ :=
  (m * 127^d) ⌈/⌉ (128^d - 127^d)

/-- Upward-rounded contribution to the variance for the same degree. -/
def polynomialVarianceCeilTerm (d m : ℕ) : ℕ :=
  (m * d * 127^d * 128^d) ⌈/⌉ (128^d - 127^d)^2

/-- Article integers U° and V° through the indicated cutoff, accumulated by degree. -/
def polynomialMomentBudgets (mass : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | d+1 =>
    let previous := polynomialMomentBudgets mass d
    (previous.1 + polynomialMeanCeilTerm (d+1) (mass (d+1)),
     previous.2 + polynomialVarianceCeilTerm (d+1) (mass (d+1)))

theorem polynomialMomentBudgets_mono {m M : ℕ → ℕ} (h : ∀ d > 0, m d ≤ M d) (n : ℕ) :
    (polynomialMomentBudgets m n).1 ≤ (polynomialMomentBudgets M n).1 ∧
    (polynomialMomentBudgets m n).2 ≤ (polynomialMomentBudgets M n).2 := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ d ih =>
    have hd : 0 < 128^(d+1) - 127^(d+1) := Nat.sub_pos_of_lt
      (Nat.pow_lt_pow_left (by decide) (by omega))
    have hceil {x y k : ℕ} (hk : 0 < k) (hxy : x ≤ y) : x ⌈/⌉ k ≤ y ⌈/⌉ k :=
      (ceilDiv_le_iff_le_mul hk).mpr (hxy.trans ((ceilDiv_le_iff_le_mul hk).mp (le_refl (y ⌈/⌉ k))))
    exact ⟨Nat.add_le_add ih.1 (hceil hd (Nat.mul_le_mul_right _ (h _ (by omega)))),
      Nat.add_le_add ih.2 (hceil (pow_pos hd _) (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (h _ (by omega))))))⟩

/-- The article's search radius R* using the actual finite-field irreducible counts. -/
noncomputable def polynomialSearchCutoff (F : Type*) [Field F] [Fintype F] : ℕ :=
  let B := polynomialMomentBudgets (fun d ↦ d * polynomialIrreducibleCount F d) 480
  480 + B.1 + ⌈Real.sqrt (7400 * (B.2 : ℝ))⌉₊

private def cutoffBelow (q e padding : ℕ) : Bool :=
  let B := polynomialMomentBudgets (q ^ ·) 480
  let base := 480 + B.1 + padding + 1
  decide (base ≤ 2^e ∧ 7400 * B.2 ≤ (2^e - base)^2)

private theorem polynomialSearchCutoff_lt_of_test (F : Type*) [Field F] [Fintype F]
    {q e padding : ℕ} (hq : Fintype.card F = q) (h : cutoffBelow q e padding = true) :
    polynomialSearchCutoff F + padding < 2^e := by
  let B := polynomialMomentBudgets (fun d ↦ d * polynomialIrreducibleCount F d) 480
  let U := polynomialMomentBudgets (q ^ ·) 480
  have hB : B.1 ≤ U.1 ∧ B.2 ≤ U.2 := polynomialMomentBudgets_mono
    (fun d hd ↦ hq ▸ degree_mul_polynomialIrreducibleCount_le (F := F) d hd) 480
  have ht : 480 + U.1 + padding + 1 ≤ 2^e ∧
      7400 * U.2 ≤ (2^e - (480 + U.1 + padding + 1))^2 := of_decide_eq_true h
  let K := 2^e - (480 + U.1 + padding + 1)
  have h2 : 7400 * B.2 ≤ K^2 := (Nat.mul_le_mul_left _ hB.2).trans ht.2
  have hs : ⌈Real.sqrt (7400 * (B.2 : ℝ))⌉₊ ≤ K := by
    apply Nat.ceil_le.mpr
    apply (Real.sqrt_le_iff).mpr
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast h2⟩
  change 480 + B.1 + ⌈Real.sqrt (7400 * (B.2 : ℝ))⌉₊ + padding < 2^e
  dsimp [K] at hs
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem numerical_cutoffs :
    cutoffBelow 2 476 13 = true ∧ cutoffBelow 3 756 0 = true ∧
    cutoffBelow 4 956 0 = true ∧ cutoffBelow 5 1110 0 = true ∧
    cutoffBelow 7 1343 0 = true := by decide +kernel

/-- Exact integer certificates for the five field sizes in the article. -/
theorem polynomialSearchCutoff_table (F : Type*) [Field F] [Fintype F] :
    (Fintype.card F = 2 → polynomialSearchCutoff F + 13 < 2^476) ∧
    (Fintype.card F = 3 → polynomialSearchCutoff F < 2^756) ∧
    (Fintype.card F = 4 → polynomialSearchCutoff F < 2^956) ∧
    (Fintype.card F = 5 → polynomialSearchCutoff F < 2^1110) ∧
    (Fintype.card F = 7 → polynomialSearchCutoff F < 2^1343) := by
  obtain ⟨h₂,h₃,h₄,h₅,h₇⟩ := numerical_cutoffs
  exact ⟨fun h ↦ polynomialSearchCutoff_lt_of_test F h h₂,
    fun h ↦ polynomialSearchCutoff_lt_of_test F h h₃,
    fun h ↦ polynomialSearchCutoff_lt_of_test F h h₄,
    fun h ↦ polynomialSearchCutoff_lt_of_test F h h₅,
    fun h ↦ polynomialSearchCutoff_lt_of_test F h h₇⟩

end GRHArticle.ProgressionFree
