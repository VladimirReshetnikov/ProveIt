import GRHArticle.ProgressionFree.FiniteGPBranchCertificate
import Mathlib.Combinatorics.Additive.AP.Three.Defs

/-!
# Certificates for maximum progression-free subsets of intervals

The weighted interval bound permits rewarding or discounting one
specified point. A single bound then also certifies whether a maximum
can include or omit that point.
-/

namespace GRHArticle.ProgressionFree

open Finset

/-- The test on a previously picked value, the new value, and a future candidate. -/
def intervalForbiddenTriple (a b c : ℕ) : Bool := decide (a ≠ b ∧ a+c=b+b)

private theorem weighted_range_filter (n : ℕ) (w : ℕ → ℕ) (B : Finset ℕ) :
    (((List.range n).filter (fun i ↦ decide (i ∈ B))).map w).sum =
      ∑ i ∈ range n, if i ∈ B then w i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : n ∈ B <;> simp [List.range_succ, ih, hn]

theorem interval_weight_le_of_branchCheck (n M : ℕ) (w : ℕ → ℕ)
    (hc : finiteGPBranchCheck w intervalForbiddenTriple M (n+1) 0 [] (List.range n) = true)
    {B : Finset ℕ} (hB : B ⊆ range n) (hf : ThreeAPFree (B : Set ℕ)) :
    ∑ i ∈ B, w i ≤ M := by
  have h := finiteGPBranchCheck_sound w intervalForbiddenTriple M (fun i ↦ decide (i ∈ B))
    (by
      intro a b c ha hb hc
      simp only [decide_eq_true_eq] at ha hb hc
      exact decide_eq_false fun ⟨hne,he⟩ ↦ hne (hf ha hb hc he))
    (n+1) (List.range n) hc
  rw [weighted_range_filter, ← sum_filter] at h
  have hEq : (range n).filter (· ∈ B) = B := by ext i; simp only [mem_filter]; exact ⟨And.right,fun hi ↦ ⟨hB hi,hi⟩⟩
  rwa [hEq] at h

/-- Unit-weight certificates bound the usual Roth number of an interval. -/
theorem rothNumberNat_le_of_branchCheck (n M : ℕ)
    (hc : finiteGPBranchCheck (fun _ ↦ 1) intervalForbiddenTriple M (n+1) 0 [] (List.range n) = true) :
    rothNumberNat n ≤ M := by
  obtain ⟨B,hB,he,hf⟩ := rothNumberNat_spec n
  simpa [he] using interval_weight_le_of_branchCheck n M (fun _ ↦ 1) hc hB hf

/-- Check that a specified point belongs to every maximizer by giving
that point weight zero. -/
theorem mem_of_interval_maximum {n M i : ℕ}
    (hc : finiteGPBranchCheck (fun x ↦ if x=i then 0 else 1) intervalForbiddenTriple
      (M-1) (n+1) 0 [] (List.range n) = true) (hM : 0 < M)
    {B : Finset ℕ} (hB : B ⊆ range n) (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = M) : i ∈ B := by
  by_contra hi
  have h := interval_weight_le_of_branchCheck n (M-1) _ hc hB hf
  have hsum : (∑ x ∈ B, if x=i then 0 else 1) = M := by
    calc
      _ = ∑ _x ∈ B, 1 := sum_congr rfl (fun x hx ↦ if_neg (show x ≠ i from fun hxi ↦ hi (hxi ▸ hx)))
      _ = _ := by simp [he]
  omega

/-- Rewarding a point by one detects when it cannot occur in any maximizer. -/
theorem notMem_of_interval_maximum {n M i : ℕ}
    (hc : finiteGPBranchCheck (fun x ↦ 1 + if x=i then 1 else 0) intervalForbiddenTriple
      M (n+1) 0 [] (List.range n) = true)
    {B : Finset ℕ} (hB : B ⊆ range n) (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = M) : i ∉ B := by
  intro hi
  have h := interval_weight_le_of_branchCheck n M _ hc hB hf
  simp [sum_add_distrib,hi,he] at h

end GRHArticle.ProgressionFree
