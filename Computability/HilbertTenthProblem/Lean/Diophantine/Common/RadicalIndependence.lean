import Diophantine.Common.RadicalField
import Diophantine.Common.RadicalWeights
import Diophantine.Common.RadicalBounds
import Mathlib.Algebra.BigOperators.Fin

/-!
# Rationality of separated radical sums

Successive products of integer weights separate square roots of integers when
each root has norm at most its weight minus one. If the resulting sum is
rational, every rational automorphism fixes every root, so every radicand is an
integer square. This argument does not assume that the square classes of the
radicands are independent.
-/

namespace Diophantine.RadicalIndependence

open RadicalField

/-- Cast the real prefix weights to the corresponding integer products. -/
theorem complex_weight (v : ℕ → ℤ) (n : ℕ) :
    (RadicalWeights.weight (fun i => (v i : ℝ)) n : ℂ) =
      ((∏ i ∈ Finset.range n, v i : ℤ) : ℂ) := by
  simp [RadicalWeights.weight]

/-- The Galois argument with an explicit lower norm bound for nonzero roots. -/
theorem isSquare_of_rational_weightedSum_of_gap
    {n : ℕ} {A v : ℕ → ℤ} {r : ℕ → RadicalField} {q : ℚ}
    (hsq : ∀ i < n, r i ^ 2 = (A i : RadicalField))
    (hv : ∀ i < n, 1 ≤ v i)
    (hbound : ∀ i < n, ‖toComplex (r i)‖ ≤ (v i : ℝ) - 1)
    (hgap : ∀ i < n, r i ≠ 0 → 1 ≤ ‖toComplex (r i)‖)
    (hsum : (∑ i ∈ Finset.range n,
      r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) =
        algebraMap ℚ RadicalField q) :
    ∀ i < n, IsSquare (A i) := by
  classical
  have hvR : ∀ i < n, (1 : ℝ) ≤ v i := by
    intro i hi
    exact_mod_cast hv i hi
  intro idx hidx
  apply isSquare_int_of_fixed (hsq idx hidx)
  intro σ
  let g : ℕ → RadicalField := fun i => if σ (r i) = r i then 0 else r i
  have hterm : ∀ i < n,
      (2 : RadicalField) * (g i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) =
        r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField) -
          σ (r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) := by
    intro i hi
    simp only [map_mul, map_intCast]
    by_cases hfix : σ (r i) = r i
    · simp only [g, if_pos hfix, hfix, zero_mul, mul_zero, sub_self]
    · have hneg : σ (r i) = -r i := (aut_eq_or_eq_neg (hsq i hi) σ).resolve_left hfix
      have hg : g i = r i := if_neg hfix
      rw [hg, hneg]
      ring
  have hzero : (∑ i ∈ Finset.range n,
      g i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) = 0 := by
    have htwo : (2 : RadicalField) * (∑ i ∈ Finset.range n,
        g i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) = 0 := by
      calc
        _ = ∑ i ∈ Finset.range n,
            (r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField) -
              σ (r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i hi => hterm i (Finset.mem_range.mp hi)
        _ = (∑ i ∈ Finset.range n,
            r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) -
              σ (∑ i ∈ Finset.range n,
                r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) := by
          rw [Finset.sum_sub_distrib, map_sum]
        _ = 0 := by rw [hsum, σ.commutes, sub_self]
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hgweighted : RadicalWeights.weightedSum (fun i => (v i : ℝ))
      (fun i => toComplex (g i)) n = 0 := by
    have hmap := congrArg toComplex hzero
    simpa only [RadicalWeights.weightedSum, complex_weight, map_sum, map_mul,
      map_intCast, map_zero] using hmap
  have hgbound : ∀ i < n, ‖toComplex (g i)‖ ≤ (v i : ℝ) - 1 := by
    intro i hi
    by_cases hfix : σ (r i) = r i
    · simp only [g, if_pos hfix, map_zero, norm_zero]
      exact sub_nonneg.mpr (hvR i hi)
    · simpa only [g, if_neg hfix] using hbound i hi
  have hggap : ∀ i < n, toComplex (g i) ≠ 0 → 1 ≤ ‖toComplex (g i)‖ := by
    intro i hi hne
    by_cases hfix : σ (r i) = r i
    · exact (hne (by simp only [g, if_pos hfix, map_zero])).elim
    · have hr : r i ≠ 0 := by
        intro hr
        apply hne
        simp only [g, if_neg hfix, hr, map_zero]
      simpa only [g, if_neg hfix] using hgap i hi hr
  have hzeroC := RadicalWeights.eq_zero_of_weightedSum_eq_zero
    hvR hgbound hggap hgweighted idx hidx
  have hzeroG : g idx = 0 := toComplex_injective (by simpa only [map_zero] using hzeroC)
  by_cases hfix : σ (r idx) = r idx
  · exact hfix
  · have hr : r idx = 0 := by simpa only [g, if_neg hfix] using hzeroG
    simp only [hr, map_zero]

/-- If a weighted sum of integer square roots is rational, every radicand
is a square. The integer weights are allowed to vary with the index. -/
theorem isSquare_of_rational_weightedSum
    {n : ℕ} {A v : ℕ → ℤ} {r : ℕ → RadicalField} {q : ℚ}
    (hsq : ∀ i < n, r i ^ 2 = (A i : RadicalField))
    (hv : ∀ i < n, 1 ≤ v i)
    (hbound : ∀ i < n, ‖toComplex (r i)‖ ≤ (v i : ℝ) - 1)
    (hsum : (∑ i ∈ Finset.range n,
      r i * ((∏ j ∈ Finset.range i, v j : ℤ) : RadicalField)) =
        algebraMap ℚ RadicalField q) :
    ∀ i < n, IsSquare (A i) := by
  apply isSquare_of_rational_weightedSum_of_gap hsq hv hbound _ hsum
  intro i hi hne
  apply RadicalBounds.one_le_norm_of_sq_eq_int (toComplex_sq (hsq i hi))
  intro hzero
  apply hne
  exact toComplex_injective (by simpa only [map_zero] using hzero)

/-- The finite-index form for the powers of a single common weight. -/
theorem isSquare_of_rational_powerSum
    {n : ℕ} {A : Fin n → ℤ} {r : Fin n → RadicalField} {W : ℤ} {q : ℚ}
    (hsq : ∀ i, r i ^ 2 = (A i : RadicalField))
    (hW : 1 ≤ W)
    (hbound : ∀ i, ‖toComplex (r i)‖ ≤ (W : ℝ) - 1)
    (hsum : (∑ i, r i * (W : RadicalField) ^ i.val) =
      algebraMap ℚ RadicalField q) :
    ∀ i, IsSquare (A i) := by
  let A' : ℕ → ℤ := fun i => if hi : i < n then A ⟨i, hi⟩ else 0
  let r' : ℕ → RadicalField := fun i => if hi : i < n then r ⟨i, hi⟩ else 0
  have hsq' : ∀ i < n, r' i ^ 2 = (A' i : RadicalField) := by
    intro i hi
    simpa only [r', A', dif_pos hi] using hsq ⟨i, hi⟩
  have hbound' : ∀ i < n, ‖toComplex (r' i)‖ ≤ (W : ℝ) - 1 := by
    intro i hi
    simpa only [r', dif_pos hi] using hbound ⟨i, hi⟩
  have hsum' : (∑ i ∈ Finset.range n,
      r' i * ((∏ _j ∈ Finset.range i, W : ℤ) : RadicalField)) =
        algebraMap ℚ RadicalField q := by
    calc
      _ = ∑ i : Fin n, r i * (W : RadicalField) ^ i.val := by
        rw [Finset.sum_range]
        apply Finset.sum_congr rfl
        intro i _
        simp only [r', dif_pos i.isLt, Fin.eta, Finset.prod_const,
          Finset.card_range, Int.cast_pow]
      _ = _ := hsum
  have hmain := isSquare_of_rational_weightedSum (n := n) (A := A')
    (r := r') (v := fun _ => W) (q := q)
    hsq' (fun _ _ => hW) hbound' hsum'
  intro i
  simpa only [A', dif_pos i.isLt, Fin.eta] using hmain i.val i.isLt

end Diophantine.RadicalIndependence
