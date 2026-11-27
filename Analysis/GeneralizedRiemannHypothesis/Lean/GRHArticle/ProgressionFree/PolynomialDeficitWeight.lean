import GRHArticle.ProgressionFree.PolynomialDeficitCertificate
import Mathlib.Data.Rat.BigOperators

/-!
# Gain against the full binary-ternary deficit rule

The geometric tail estimate extends the finite weighted certificate to the
actual infinite generating value in the polynomial-ring replacement lemma.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- The translated finite deficit set improves the full ternary generating
value at `z = 127/128` by more than the article's margin `3/200`. -/
theorem polynomialDeficitWeight_gain_over_greedy :
    (3 : ℝ) / 200 <
      (∑ d ∈ polynomialDeficitWitness, ((127 : ℝ) / 128) ^ d) -
        ∑' d : ℕ, greedyExponents.indicator (fun d ↦ ((127 : ℝ) / 128) ^ d) d := by
  classical
  let z : ℝ := 127 / 128
  let f : ℕ → ℝ := greedyExponents.indicator (fun d ↦ z ^ d)
  have hz₀ : 0 ≤ z := by norm_num [z]
  have hz₁ : z < 1 := by norm_num [z]
  have hgeom : Summable (fun d : ℕ ↦ z ^ d) := summable_geometric_of_lt_one hz₀ hz₁
  have hfle (d : ℕ) : 0 ≤ f d ∧ f d ≤ z ^ d := by
    by_cases hd : d ∈ greedyExponents
    · simp [f, Set.indicator_of_mem hd, pow_nonneg hz₀]
    · simp [f, Set.indicator_of_notMem hd, pow_nonneg hz₀]
  have hfs : Summable f :=
    Summable.of_nonneg_of_le (fun d ↦ (hfle d).1) (fun d ↦ (hfle d).2) hgeom
  have hprefix : (∑ d ∈ Finset.range 2187, f d) =
      ∑ d ∈ ternaryDeficitPrefix, z ^ d := by
    have hsub : ternaryDeficitPrefix ⊆ Finset.range 2187 := fun d hd ↦
      Finset.mem_range.mpr ((mem_ternaryDeficitPrefix d).mp hd).1
    calc
      _ = ∑ d ∈ ternaryDeficitPrefix, f d := by
        symm
        apply Finset.sum_subset hsub
        intro d hd hnot
        have hngreedy : d ∉ greedyExponents := fun h ↦
          hnot ((mem_ternaryDeficitPrefix d).mpr ⟨Finset.mem_range.mp hd, h⟩)
        exact Set.indicator_of_notMem hngreedy _
      _ = _ := Finset.sum_congr rfl fun d hd ↦
        Set.indicator_of_mem ((mem_ternaryDeficitPrefix d).mp hd).2 _
  have htail : (∑' d : ℕ, f (d + 2187)) ≤ (128 : ℝ) * z ^ 2187 := by
    have hfs' := (summable_nat_add_iff 2187).mpr hfs
    have hgeom' := (summable_nat_add_iff 2187).mpr hgeom
    calc
      _ ≤ ∑' d : ℕ, z ^ (d + 2187) :=
        hfs'.tsum_le_tsum (fun d ↦ (hfle (d + 2187)).2) hgeom'
      _ = _ := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one hz₀ hz₁]
        have h : (1 - z)⁻¹ = (128 : ℝ) := by norm_num [z]
        rw [h]
  have hcut : (128 : ℝ) * z ^ 2187 < 1 / 100000 := by
    simpa [z, Rat.cast_div] using (Rat.cast_lt (K := ℝ)).mpr polynomialDeficitTail_bound
  have hgain :
      (16 : ℝ) / 1000 < (∑ d ∈ polynomialDeficitWitness, z ^ d) -
        ∑ d ∈ ternaryDeficitPrefix, z ^ d := by
    simpa [z, Rat.cast_div, Rat.cast_sum] using
      (Rat.cast_lt (K := ℝ)).mpr polynomialDeficitWeight_gain
  have hsplit := hfs.sum_add_tsum_nat_add 2187
  rw [hprefix] at hsplit
  change (3 : ℝ) / 200 < (∑ d ∈ polynomialDeficitWitness, z ^ d) - (∑' d, f d)
  linarith only [hgain, htail.trans_lt hcut, hsplit]

end GRHArticle.ProgressionFree
