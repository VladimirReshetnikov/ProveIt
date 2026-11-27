import GRHArticle.ProgressionFree.NumberFieldIdeals.ValuationCylinders
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fintype.Option

/-!
# Summing independent local exponent weights

The product of nonnegative summable exponent distributions on a finite
set of primes defines a summable distribution on all exponent tuples.
Its total mass is the product of the one-prime masses.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal Finset IsDedekindDomain

set_option maxHeartbeats 800000 in
/-- Factor the sum over all exponent vectors into its one-coordinate sums. -/
theorem hasSum_finiteExponentProduct {ι : Type*} [Fintype ι] (w : ι → ℕ → ℝ) (d : ι → ℝ)
    (hw : ∀ i, HasSum (w i) (d i)) (hpos : ∀ i n, 0 ≤ w i n) :
    HasSum (fun v : ι → ℕ ↦ ∏ i, w i (v i)) (∏ i, d i) := by
  classical
  let P := fun (t : Type _) [Fintype t] ↦ ∀ (w : t → ℕ → ℝ) (d : t → ℝ),
    (∀ i, HasSum (w i) (d i)) → (∀ i n, 0 ≤ w i n) →
    HasSum (fun v : t → ℕ ↦ ∏ i, w i (v i)) (∏ i, d i)
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι w d hw hpos
  · intro α β _ e ih w d hw hp
    letI := Fintype.ofEquiv β e.symm
    have h := ih (fun i ↦ w (e i)) (fun i ↦ d (e i)) (fun i ↦ hw (e i)) (fun i ↦ hp (e i))
    let E : (β → ℕ) ≃ (α → ℕ) := e.symm.arrowCongr (Equiv.refl ℕ)
    rw [e.prod_comp d] at h
    apply (E.hasSum_iff).mpr h |>.congr_fun
    intro v
    exact (e.prod_comp (fun i ↦ w i (v i))).symm
  · intro w d _ _
    simp
  · intro α _ ih w d hw hp
    have ht := ih (fun i ↦ w (some i)) (fun i ↦ d (some i)) (fun i ↦ hw (some i)) (fun i ↦ hp (some i))
    have hs₁ : Summable (fun n ↦ ‖w none n‖) := by
      simpa only [Real.norm_of_nonneg (hp none _)] using (hw none).summable
    have hs₂ : Summable (fun v : α → ℕ ↦ ‖∏ i, w (some i) (v i)‖) := by
      simpa only [Real.norm_of_nonneg (Finset.prod_nonneg (fun i _ ↦ hp (some i) _))] using ht.summable
    have h := (hw none).mul ht (summable_mul_of_summable_norm hs₁ hs₂)
    rw [Fintype.prod_option]
    let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd
    apply (E.hasSum_iff.mpr h).congr_fun
    intro v
    exact Fintype.prod_option (fun i ↦ w i (v i))

end GRHArticle.ProgressionFree.NumberFieldIdeals
