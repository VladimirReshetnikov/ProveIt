import GRHArticle.ProgressionFree.PolynomialBlocks
import GRHArticle.ProgressionFree.PolynomialDeficitSet

/-!
# Counting the unmodified polynomial degree layers
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped BigOperators Classical

/-- Polynomials of exact degree `n` over a finite field, including every
nonzero leading coefficient. -/
noncomputable def polynomialDegreeLayer (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Finset (Polynomial F) := by
  classical
  exact polynomialDegreeLTFinset F (n+1) \ polynomialDegreeLTFinset F n

variable {F : Type*} [Field F] [Fintype F]

theorem mem_polynomialDegreeLayer {f : Polynomial F} {n : ℕ} :
    f ∈ polynomialDegreeLayer F n ↔ f ≠ 0 ∧ f.natDegree = n := by
  classical
  simp only [polynomialDegreeLayer, Finset.mem_sdiff, mem_polynomialDegreeLTFinset]
  by_cases hf : f = 0
  · simp [hf]
  · simp only [degree_eq_natDegree hf, Nat.cast_lt, hf, ne_eq, not_false_eq_true, true_and]
    omega

theorem card_polynomialDegreeLayer (n : ℕ) :
    (polynomialDegreeLayer F n).card = (Fintype.card F - 1) * Fintype.card F ^ n := by
  classical
  have hsub : polynomialDegreeLTFinset F n ⊆ polynomialDegreeLTFinset F (n+1) := by
    intro f hf
    apply mem_polynomialDegreeLTFinset.mpr
    exact (mem_polynomialDegreeLTFinset.mp hf).trans (Nat.cast_lt.mpr (Nat.lt_succ_self n))
  rw [polynomialDegreeLayer, Finset.card_sdiff_of_subset hsub, card_polynomialDegreeLTFinset,
    card_polynomialDegreeLTFinset, pow_succ', Nat.sub_mul, one_mul]

/-- The exact baseline count before modifying the rough classes at cutoff `N`. -/
theorem card_polynomialDeficitSet (A : Set ℕ) (N : ℕ) :
    (Finset.filter (fun f ↦ f ∈ polynomialDeficitSet A N) (polynomialDegreeLTFinset F (N+1))).card =
      ∑ d ∈ (Finset.range (N+1)).filter (· ∈ A), (Fintype.card F - 1) * Fintype.card F ^ (N-d) := by
  classical
  let S := (polynomialDegreeLTFinset F (N + 1)).filter (· ∈ polynomialDeficitSet A N)
  let D := (Finset.range (N+1)).filter (· ∈ A)
  have hmaps : (S : Set (Polynomial F)).MapsTo (fun f ↦ N - f.natDegree) D := by
    intro f hf
    have hd := (Finset.mem_filter.mp hf).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)), hd.2.2⟩
  change S.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdr, hdA⟩ := Finset.mem_filter.mp hd
  have hdN := Finset.mem_range.mp hdr
  rw [← card_polynomialDegreeLayer]
  congr 1
  ext f
  simp only [S, Finset.mem_filter, mem_polynomialDegreeLTFinset, mem_polynomialDegreeLayer]
  constructor
  · rintro ⟨⟨_, hn, hdeg, _⟩, heq⟩
    exact ⟨hn, by omega⟩
  · rintro ⟨hn, hdeg⟩
    have heq : N - f.natDegree = d := by omega
    refine ⟨⟨?_, hn, by omega, heq ▸ hdA⟩, heq⟩
    rw [degree_eq_natDegree hn, Nat.cast_lt]
    omega

/-- Exact proportion of any degree-deficit rule in the finite degree ball. -/
theorem polynomialBallProportion_deficit (A : Set ℕ) (N : ℕ) :
    polynomialBallProportion (polynomialDeficitSet (F := F) A N) N =
      (1 - (Fintype.card F : ℝ)⁻¹) *
        ∑ d ∈ (Finset.range (N+1)).filter (· ∈ A), (Fintype.card F : ℝ)⁻¹ ^ d := by
  classical
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold polynomialBallProportion
  rw [card_polynomialDeficitSet, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdN := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  have hsplit : (Fintype.card F : ℝ) ^ (N+1) =
      (Fintype.card F : ℝ) ^ (N-d) * (Fintype.card F : ℝ) ^ d * Fintype.card F := by
    rw [← pow_add, show N-d+d=N by omega, pow_succ]
  rw [Nat.cast_mul, Nat.cast_sub (by exact Fintype.card_pos), Nat.cast_pow, Nat.cast_one,
    hsplit, inv_pow]
  field_simp

/-- The baseline ball proportions tend to the article's weighted sum for
every choice of the allowed deficits. -/
theorem tendsto_polynomialBallProportion_deficit (A : Set ℕ) :
    Tendsto (fun N ↦ polynomialBallProportion (polynomialDeficitSet (F := F) A N) N) atTop
      (𝓝 ((1 - (Fintype.card F : ℝ)⁻¹) *
        ∑' d : ℕ, A.indicator (fun d ↦ (Fintype.card F : ℝ)⁻¹ ^ d) d)) := by
  classical
  let z := (Fintype.card F : ℝ)⁻¹
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hz : 0 ≤ z := inv_nonneg.mpr (by positivity)
  have hgeom : Summable (fun d : ℕ ↦ z ^ d) :=
    summable_geometric_of_lt_one hz (inv_lt_one_of_one_lt₀ hq)
  have hsum := hgeom.indicator A
  have heq (N : ℕ) : (∑ d ∈ (Finset.range (N+1)).filter (· ∈ A), z ^ d) =
      ∑ d ∈ Finset.range (N+1), A.indicator (fun d ↦ z ^ d) d := by
    rw [Finset.sum_filter]
    rfl
  simp_rw [polynomialBallProportion_deficit, ← show z = (Fintype.card F : ℝ)⁻¹ from rfl, heq]
  exact tendsto_const_nhds.mul (hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))

end GRHArticle.ProgressionFree
