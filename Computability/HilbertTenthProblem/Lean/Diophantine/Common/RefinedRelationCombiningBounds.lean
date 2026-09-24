import Diophantine.Common.RefinedRelationCombiningPolynomial
import Diophantine.Common.RadicalIndependence

/-!
# Finite prefix weights for refined relation combining

These interfaces transport the separated-weight Galois argument to the finite
index convention of the explicit polynomial, and prove its positive offset.
-/

namespace Diophantine.RefinedRelationCombiningBounds

open RefinedRelationCombiningPolynomial RadicalField

theorem prefix_succ {q : ℕ} {S : Type*} [CommMonoid S]
    (V : Fin q → S) {m : ℕ} (hm : m < q) :
    weightPrefix V (m + 1) = weightPrefix V m * V ⟨m, hm⟩ := by
  classical
  have heq : (Finset.univ.filter fun j : Fin q => j.val < m + 1) =
      insert ⟨m, hm⟩ (Finset.univ.filter fun j : Fin q => j.val < m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff]
    omega
  unfold weightPrefix
  rw [heq, Finset.prod_insert (by simp)]
  exact mul_comm _ _

/-- Extend a finite family by ones without changing any valid prefix. -/
theorem prefix_eq_range {q : ℕ} {S : Type*} [CommMonoid S]
    (V : Fin q → S) {m : ℕ} (hm : m ≤ q) :
    weightPrefix V m = ∏ j ∈ Finset.range m, (if hj : j < q then V ⟨j, hj⟩ else 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmq : m < q := by omega
      rw [prefix_succ V hmq, Finset.prod_range_succ, dif_pos hmq, ih (by omega)]

private theorem one_le_offset_range {v r : ℕ → ℤ} {n : ℕ}
    (hv : ∀ i < n, 1 ≤ v i) (hr : ∀ i < n, |r i| ≤ v i - 1) :
    1 ≤ (∏ i ∈ Finset.range n, v i) +
      ∑ i ∈ Finset.range n, r i * ∏ j ∈ Finset.range i, v j := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprefix := ih (fun i hi => hv i (by omega)) (fun i hi => hr i (by omega))
      have hlast := (abs_le.mp (hr n (by omega))).1
      have hprod : 0 ≤ ∏ i ∈ Finset.range n, v i := by
        exact Finset.prod_nonneg fun i hi => by
          have := hv i (by have := Finset.mem_range.mp hi; omega)
          omega
      have hmul := mul_nonneg (show 0 ≤ r n + (v n - 1) by omega) hprod
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      nlinarith

theorem one_le_offset {q : ℕ} {V r : Fin q → ℤ}
    (hv : ∀ i, 1 ≤ V i) (hr : ∀ i, |r i| ≤ V i - 1) :
    1 ≤ weightPrefix V q + ∑ i, r i * weightPrefix V i.val := by
  let v' : ℕ → ℤ := fun i => if hi : i < q then V ⟨i, hi⟩ else 1
  let r' : ℕ → ℤ := fun i => if hi : i < q then r ⟨i, hi⟩ else 0
  have hv' : ∀ i < q, 1 ≤ v' i := by
    intro i hi
    simpa only [v', dif_pos hi] using hv ⟨i, hi⟩
  have hr' : ∀ i < q, |r' i| ≤ v' i - 1 := by
    intro i hi
    simpa only [v', r', dif_pos hi] using hr ⟨i, hi⟩
  have h := one_le_offset_range hv' hr'
  have heq : (∏ i ∈ Finset.range q, v' i) +
      ∑ i ∈ Finset.range q, r' i * ∏ j ∈ Finset.range i, v' j =
      weightPrefix V q + ∑ i, r i * weightPrefix V i.val := by
    rw [prefix_eq_range V (le_refl q)]
    congr 1
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [r', dif_pos i.isLt, Fin.eta, prefix_eq_range V i.isLt.le, v']
  rwa [heq] at h

theorem isSquare_of_rational_prefixSum
    {q : ℕ} {A V : Fin q → ℤ} {r : Fin q → RadicalField} {u : ℚ}
    (hsq : ∀ i, r i ^ 2 = (A i : RadicalField))
    (hv : ∀ i, 1 ≤ V i)
    (hbound : ∀ i, ‖toComplex (r i)‖ ≤ (V i : ℝ) - 1)
    (hsum : (∑ i, r i * ((weightPrefix V i.val : ℤ) : RadicalField)) =
      algebraMap ℚ RadicalField u) : ∀ i, IsSquare (A i) := by
  let A' : ℕ → ℤ := fun i => if hi : i < q then A ⟨i, hi⟩ else 0
  let v' : ℕ → ℤ := fun i => if hi : i < q then V ⟨i, hi⟩ else 1
  let r' : ℕ → RadicalField := fun i => if hi : i < q then r ⟨i, hi⟩ else 0
  have hsq' : ∀ i < q, r' i ^ 2 = (A' i : RadicalField) := by
    intro i hi
    simpa only [r', A', dif_pos hi] using hsq ⟨i, hi⟩
  have hv' : ∀ i < q, 1 ≤ v' i := by
    intro i hi
    simpa only [v', dif_pos hi] using hv ⟨i, hi⟩
  have hb' : ∀ i < q, ‖toComplex (r' i)‖ ≤ (v' i : ℝ) - 1 := by
    intro i hi
    simpa only [r', v', dif_pos hi] using hbound ⟨i, hi⟩
  have hs' : (∑ i ∈ Finset.range q,
      r' i * ((∏ j ∈ Finset.range i, v' j : ℤ) : RadicalField)) =
      algebraMap ℚ RadicalField u := by
    calc
      _ = ∑ i : Fin q, r i * ((weightPrefix V i.val : ℤ) : RadicalField) := by
        rw [Finset.sum_range]
        apply Finset.sum_congr rfl
        intro i _
        simp only [r', dif_pos i.isLt, Fin.eta, prefix_eq_range V i.isLt.le, v']
      _ = _ := hsum
  have hmain := RadicalIndependence.isSquare_of_rational_weightedSum hsq' hv' hb' hs'
  intro i
  simpa only [A', dif_pos i.isLt, Fin.eta] using hmain i.val i.isLt

end Diophantine.RefinedRelationCombiningBounds
