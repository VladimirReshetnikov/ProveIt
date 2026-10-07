import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation

namespace OAI

section

namespace Erdos3

def allocatedCandidateNativeMajorBudget (pNative v : ℝ) : ℝ :=
  productNiltestBudget pNative + pNative + v + 2

theorem allocatedCandidateNativeMajorBudget_bounds {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    0 ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      pNative ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      productNiltestBudget pNative ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      v ≤ allocatedCandidateNativeMajorBudget pNative v := by
  have hproduct : 0 ≤ productNiltestBudget pNative :=
    (sq_nonneg (pNative + 2)).trans (productNiltestBudget_geometry hpNative)
  unfold allocatedCandidateNativeMajorBudget
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedCandidateNativeMajorBudget_nonneg {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    0 ≤ allocatedCandidateNativeMajorBudget pNative v :=
  (allocatedCandidateNativeMajorBudget_bounds hpNative hv).1

theorem allocatedCandidateNativeMajorBudget_native_le {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    pNative ≤ allocatedCandidateNativeMajorBudget pNative v :=
  (allocatedCandidateNativeMajorBudget_bounds hpNative hv).2.1

theorem allocatedCandidateNativeMajorBudget_product_le {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    productNiltestBudget pNative ≤ allocatedCandidateNativeMajorBudget pNative v :=
  (allocatedCandidateNativeMajorBudget_bounds hpNative hv).2.2.1

theorem allocatedCandidateNativeMajorBudget_parameter_le {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    v ≤ allocatedCandidateNativeMajorBudget pNative v :=
  (allocatedCandidateNativeMajorBudget_bounds hpNative hv).2.2.2

theorem allocatedCandidateNativeMajorBudget_mono {pNative qNative v w : ℝ}
    (hpNative : 0 ≤ pNative) (hNative : pNative ≤ qNative) (hvw : v ≤ w) :
    allocatedCandidateNativeMajorBudget pNative v ≤
      allocatedCandidateNativeMajorBudget qNative w := by
  unfold allocatedCandidateNativeMajorBudget productNiltestBudget productObservableLipBudget
  gcongr

theorem exists_allocated_candidate_native_major_budget (Cnative : ℕ) :
    ∃ Cmajor : ℕ, 2 ≤ Cmajor ∧ ∀ t v pNative : ℝ,
      0 ≤ t → 0 ≤ v → v ≤ t → 0 ≤ pNative →
      pNative ≤ (t + Cnative) ^ Cnative →
      allocatedCandidateNativeMajorBudget pNative v ≤ (t + Cmajor) ^ Cmajor := by
  let X : Polynomial ℕ := Polynomial.X
  let N := (X + Polynomial.C Cnative) ^ Cnative
  let P := (N + 2) ^ 2 + N + (N + (N ^ 2 + N + 3) ^ 2) + N ^ 2 + 4 + N + X + 2
  obtain ⟨Cmajor, hCmajor, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨Cmajor, hCmajor, ?_⟩
  intro t v pNative ht _hv hvt hpNative hNative
  apply (allocatedCandidateNativeMajorBudget_mono hpNative hNative hvt).trans
  simpa [P, N, X, Polynomial.eval₂_pow, allocatedCandidateNativeMajorBudget,
    productNiltestBudget, productObservableLipBudget] using hbudget t ht

theorem exists_allocated_candidate_promoted_native_major_budget (Cnative : ℕ) :
    ∃ Cmajor : ℕ, 2 ≤ Cmajor ∧ ∀ t v pNative : ℝ,
      0 ≤ t → 0 ≤ v → v ≤ t → 0 ≤ pNative →
      pNative ≤ (t + Cnative) ^ Cnative →
      allocatedCandidateNativeMajorBudget (pNative + v + 2) v ≤
        (t + Cmajor) ^ Cmajor := by
  let X : Polynomial ℕ := Polynomial.X
  let N := (X + Polynomial.C Cnative) ^ Cnative + X + 2
  let P := (N + 2) ^ 2 + N + (N + (N ^ 2 + N + 3) ^ 2) + N ^ 2 + 4 + N + X + 2
  obtain ⟨Cmajor, hCmajor, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨Cmajor, hCmajor, ?_⟩
  intro t v pNative ht hv hvt hpNative hNative
  have hpromoted : pNative + v + 2 ≤ (t + Cnative) ^ Cnative + t + 2 := by
    linarith
  apply (allocatedCandidateNativeMajorBudget_mono (by linarith) hpromoted hvt).trans
  simpa [P, N, X, Polynomial.eval₂_pow, allocatedCandidateNativeMajorBudget,
    productNiltestBudget, productObservableLipBudget] using hbudget t ht

end Erdos3

end

end OAI
