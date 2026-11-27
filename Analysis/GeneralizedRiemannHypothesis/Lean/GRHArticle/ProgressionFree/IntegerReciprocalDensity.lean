import GRHArticle.ProgressionFree.IntegerDensityExtrema
import GRHArticle.ProgressionFree.IntegerPrefixTransfer
import Mathlib.Analysis.PSeries

/-!
# Transferring reciprocal-mass comparisons to natural densities

Partial summation writes the reciprocal mass as a boundary term and a
harmonically weighted sum of the ordinary proportions. The divergence of
the harmonic series detects any strict inequality between density limits.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Finset
open scoped BigOperators Classical

/-- The reciprocal mass of the positive members of a set up to a cutoff. -/
noncomputable def reciprocalMassUpTo (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ integerPrefixSlice A N, (n : ℝ)⁻¹

private theorem countUpTo_eq_card_prefixSlice (A : Set ℕ) (N : ℕ) :
    countUpTo A N = (integerPrefixSlice A N).card := rfl

private theorem integerPrefixSlice_succ (A : Set ℕ) (N : ℕ) :
    integerPrefixSlice A (N+1) =
      if N+1 ∈ A then insert (N+1) (integerPrefixSlice A N) else integerPrefixSlice A N := by
  have hI : integerPrefix (N+1) = insert (N+1) (integerPrefix N) := by
    ext n
    simp only [integerPrefix, mem_Icc, mem_insert]
    omega
  simp only [integerPrefixSlice, hI, filter_insert]

private theorem not_mem_prefixAtBefore (A : Set ℕ) (N : ℕ) :
    N+1 ∉ integerPrefixSlice A N := by
  intro h
  have hk := (mem_Icc.mp (mem_filter.mp h).1).2
  omega

private theorem reciprocalMassUpTo_succ (A : Set ℕ) (N : ℕ) :
    reciprocalMassUpTo A (N+1) =
      reciprocalMassUpTo A N + if N+1 ∈ A then ((N+1 : ℕ) : ℝ)⁻¹ else 0 := by
  unfold reciprocalMassUpTo
  rw [integerPrefixSlice_succ]
  split_ifs <;> simp [sum_insert, not_mem_prefixAtBefore, add_comm]

private theorem countUpTo_succ (A : Set ℕ) (N : ℕ) :
    countUpTo A (N+1) = countUpTo A N + if N+1 ∈ A then 1 else 0 := by
  simp only [countUpTo_eq_card_prefixSlice]
  rw [integerPrefixSlice_succ]
  split_ifs <;> simp [card_insert_of_notMem, not_mem_prefixAtBefore]

theorem reciprocalMassUpTo_partial_summation (A : Set ℕ) (N : ℕ) :
    reciprocalMassUpTo A N = (countUpTo A N : ℝ) / ((N : ℝ)+1) +
      ∑ k ∈ range N, densityUpTo A (k+1) / ((k : ℝ)+2) := by
  induction N with
  | zero => simp [reciprocalMassUpTo, countUpTo, integerPrefixSlice, integerPrefix]
  | succ N ih =>
    rw [reciprocalMassUpTo_succ, ih, sum_range_succ]
    unfold densityUpTo
    simp only [countUpTo_succ A N, Nat.cast_add, Nat.cast_one]
    have h₁ : (N:ℝ)+1 ≠ 0 := by positivity
    have h₂ : (N:ℝ)+2 ≠ 0 := by positivity
    have he : (N:ℝ)+1+1 = (N:ℝ)+2 := by ring
    rw [he]
    split_ifs <;> push_cast <;> field_simp <;> ring

/-- A uniform reciprocal-mass upper bound passes to the ordinary density
limits. -/
theorem naturalDensity_le_of_reciprocalMass_le {A R : Set ℕ} {a c M : ℝ}
    (ha : HasNaturalDensity A a) (hc : HasNaturalDensity R c)
    (h : ∀ N, reciprocalMassUpTo A N ≤ M * reciprocalMassUpTo R N) :
    a ≤ M*c := by
  by_contra! hlt
  let f (k : ℕ) := (densityUpTo A (k+1) - M * densityUpTo R (k+1)) / ((k:ℝ)+2)
  let ε := (a-M*c)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hshift : Tendsto (fun k : ℕ ↦ k+1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun k ↦ ⟨k, fun n hn ↦ by omega⟩
  have ht := (ha.comp hshift).sub ((hc.comp hshift).const_mul M)
  have hev : ∀ᶠ k : ℕ in atTop, ε ≤ densityUpTo A (k+1) - M * densityUpTo R (k+1) :=
    (ht.eventually (Ioi_mem_nhds (show ε < a-M*c by dsimp [ε]; linarith))).mono
      (fun _ hk ↦ hk.le)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  have habs (N : ℕ) : (∑ k ∈ range N, f k) ≤ |M| := by
    have hsum : (∑ k ∈ range N, f k) =
        (∑ k ∈ range N, densityUpTo A (k+1)/((k:ℝ)+2)) -
          M * ∑ k ∈ range N, densityUpTo R (k+1)/((k:ℝ)+2) := by
      simp only [f, sub_div, mul_div_assoc, sum_sub_distrib, mul_sum]
    have hbound := h N
    rw [reciprocalMassUpTo_partial_summation, reciprocalMassUpTo_partial_summation, mul_add] at hbound
    have hR₀ : 0 ≤ (countUpTo R N : ℝ) / ((N : ℝ)+1) := by positivity
    have hA₀ : 0 ≤ (countUpTo A N : ℝ) / ((N : ℝ)+1) := by positivity
    have hR₁ : (countUpTo R N : ℝ) / ((N : ℝ)+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      rw [one_mul]
      exact (by exact_mod_cast countUpTo_le_cutoff R N : (countUpTo R N : ℝ) ≤ N).trans
        (by linarith)
    have hprod : M * ((countUpTo R N : ℝ) / ((N : ℝ)+1)) ≤ |M| :=
      (mul_le_mul_of_nonneg_right (le_abs_self M) hR₀).trans
        (by simpa using mul_le_mul_of_nonneg_left hR₁ (abs_nonneg M))
    rw [hsum]
    linarith only [hbound, hprod, hA₀]
  let w (k : ℕ) := 1/((k:ℝ)+1)
  let initial := ∑ i ∈ range K, f i
  let headWeight := ∑ i ∈ range (K+1), w i
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (|M|-initial)/ε+headWeight < ∑ i ∈ range n, w i :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (Ioi_mem_atTop ((|M|-initial)/ε+headWeight))
  obtain ⟨n, hn, hnlarge⟩ := ((eventually_ge_atTop (K+1)).and hlarge).exists
  obtain ⟨j, rfl⟩ : ∃ j, n = (K+1)+j := ⟨n-(K+1), by omega⟩
  rw [sum_range_add] at hnlarge
  have hbig : |M|-initial < ε * (∑ i ∈ range j, w ((K+1)+i)) := by
    have hd : (|M|-initial)/ε < ∑ i ∈ range j, w ((K+1)+i) := by
      change _ < headWeight + _ at hnlarge
      linarith
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hd
  have htail : ε * (∑ i ∈ range j, w ((K+1)+i)) ≤ ∑ i ∈ range j, f (K+i) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hx := hK (K+i) (by omega)
    have hw : w ((K+1)+i) = 1/(((K+i:ℕ):ℝ)+2) := by
      dsimp [w]
      push_cast
      ring
    rw [hw, mul_one_div]
    exact div_le_div_of_nonneg_right hx (by positivity)
  have hbounded := habs (K+j)
  rw [sum_range_add] at hbounded
  change initial + _ ≤ _ at hbounded
  linarith only [hbounded, hbig, htail]

end GRHArticle.ProgressionFree
