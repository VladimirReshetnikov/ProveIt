import GRHArticle.ProgressionFree.IntegerSmoothPrefixIncrements
import GRHArticle.ProgressionFree.IntegerRoughTemplateDensity

/-!
# The smooth upper bound for integer upper density

The admissible part of each rough fiber can contain only as many smooth
factors as the finite optimizer for its size. The jump set of those optima
provides a single comparison template with exactly the limiting proportion
`U_Y`.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

private theorem mem_prefixSlice {A : Set ℕ} {N n : ℕ} :
    n ∈ integerPrefixSlice A N ↔ n ∈ integerPrefix N ∧ n ∈ A := by
  simp only [integerPrefixSlice, mem_filter]

private noncomputable def roughSmoothFiber (A : Set ℕ) (Y N g : ℕ) : Finset ℕ :=
  (integerPrefixSlice (Nat.smoothNumbers (Y+1)) (N/g)).filter (fun s ↦ g*s ∈ A)

private theorem card_roughSmoothFiber (A : Set ℕ) (Y N : ℕ) {g : ℕ}
    (hg : g ∈ integerRoughNumbers Y) :
    (roughSmoothFiber A Y N g).card =
      ((integerPrefixSlice A N).filter (fun n ↦ integerRoughPart Y n = g)).card := by
  have hg₀ := Nat.pos_of_ne_zero hg.1
  apply Finset.card_bij (fun s _ ↦ g*s)
  · intro s hs
    obtain ⟨hs, hA⟩ := mem_filter.mp hs
    obtain ⟨hsB, hsS⟩ := mem_prefixSlice.mp hs
    obtain ⟨hs₀, hsN⟩ := mem_Icc.mp hsB
    refine mem_filter.mpr ⟨mem_prefixSlice.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hg₀ hs₀, ?_⟩, hA⟩,
      integerRoughPart_mul_of_parts hg hsS⟩
    exact Nat.mul_comm s g ▸ (Nat.le_div_iff_mul_le hg₀).mp hsN
  · intro a _ b _ h
    exact Nat.mul_left_cancel hg₀ h
  · intro n hn
    obtain ⟨hn, hgn⟩ := mem_filter.mp hn
    obtain ⟨hnB, hnA⟩ := mem_prefixSlice.mp hn
    obtain ⟨hn₀, hnN⟩ := mem_Icc.mp hnB
    let s := integerSmoothPart Y n
    have hsS : s ∈ Nat.smoothNumbers (Y+1) := integerSmoothPart_mem Y n
    have hp : g*s = n := by
      rw [← hgn, mul_comm]
      exact integerSmoothPart_mul_roughPart Y (Nat.ne_of_gt hn₀)
    have hsN : s ≤ N/g := (Nat.le_div_iff_mul_le hg₀).mpr (by rwa [mul_comm, hp])
    exact ⟨s, mem_filter.mpr ⟨mem_prefixSlice.mpr ⟨mem_Icc.mpr
      ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hsS), hsN⟩, hsS⟩, hp.symm ▸ hnA⟩, hp⟩

private theorem countUpTo_eq_sum_roughSmoothFiber (A : Set ℕ) (Y N : ℕ) :
    countUpTo A N = ∑ g ∈ integerPrefixSlice (integerRoughNumbers Y) N,
      (roughSmoothFiber A Y N g).card := by
  let B := integerPrefixSlice A N
  let G := integerPrefixSlice (integerRoughNumbers Y) N
  have hmaps : Set.MapsTo (integerRoughPart Y) (B : Set ℕ) G := by
    intro n hn
    obtain ⟨hnB,_⟩ := mem_prefixSlice.mp hn
    obtain ⟨hn₀, hnN⟩ := mem_Icc.mp hnB
    have hg := integerRoughPart_mem Y n
    have hsp := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (integerSmoothPart_mem Y n))
    have hp := integerSmoothPart_mul_roughPart Y (Nat.ne_of_gt hn₀)
    have hgN := (Nat.le_mul_of_pos_left (integerRoughPart Y n) hsp).trans (hp.symm ▸ hnN)
    exact mem_prefixSlice.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hg.1, hgN⟩, hg⟩
  change B.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  exact Finset.sum_congr rfl (fun g hg ↦ (card_roughSmoothFiber A Y N (mem_prefixSlice.mp hg).2).symm)

private theorem roughSmoothFiber_admissible {A : Set ℕ} {integral : Bool}
    (hA : IntegerPrefixAdmissible integral A) (Y N : ℕ) {g : ℕ} (hg : 0 < g) :
    IntegerPrefixAdmissible integral (roughSmoothFiber A Y N g : Set ℕ) := by
  intro a b c ha hb hc hab hbc he hdiv
  have ha' : g*a ∈ A := (mem_filter.mp ha).2
  have hb' : g*b ∈ A := (mem_filter.mp hb).2
  have hc' : g*c ∈ A := (mem_filter.mp hc).2
  refine hA ha' hb' hc' (Nat.mul_lt_mul_of_pos_left hab hg) (Nat.mul_lt_mul_of_pos_left hbc hg) ?_ ?_
  · calc
      (g*a)*(g*c) = g*g*(a*c) := by ring
      _ = g*g*(b*b) := by rw [he]
      _ = (g*b)*(g*b) := by ring
  · intro hi
    obtain ⟨r, hr⟩ := hdiv hi
    exact ⟨r, by rw [hr, mul_assoc]⟩

/-- At every cutoff the selected count is bounded by that of the unrestricted
rough products with the smooth jump set. -/
theorem countUpTo_le_integerSmoothJumpProducts {integral : Bool} {A : Set ℕ}
    (hA : IntegerPrefixAdmissible integral A) (Y N : ℕ) :
    countUpTo A N ≤ countUpTo
      (integerRoughTemplateProducts (integerRoughNumbers Y) (integerSmoothPrefixJumps integral Y)) N := by
  let D := integerSmoothPrefixJumps integral Y
  let T := integerRoughTemplateProducts (integerRoughNumbers Y) D
  have hD := integerSmoothPrefixJumps_subset_smoothNumbers integral Y
  change countUpTo A N ≤ countUpTo T N
  rw [countUpTo_eq_sum_roughSmoothFiber A Y, countUpTo_eq_sum_roughSmoothFiber T Y]
  apply Finset.sum_le_sum
  intro g hg
  have hg' := (mem_prefixSlice.mp hg).2
  have hg₀ := Nat.pos_of_ne_zero hg'.1
  calc
    _ ≤ integerSmoothPrefixMaximum integral Y (N/g) :=
      card_le_integerSmoothPrefixMaximum (filter_subset _ _) (roughSmoothFiber_admissible hA Y N hg₀)
    _ = (integerPrefixSlice D (N/g)).card := (card_integerPrefixSlice_smoothPrefixJumps integral Y _).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro s hs
      obtain ⟨hsB, hsD⟩ := mem_prefixSlice.mp hs
      exact mem_filter.mpr ⟨mem_prefixSlice.mpr ⟨hsB,hD hsD⟩, g,s,hg',hsD,rfl⟩

/-- Every admissible set has upper density at most the smooth upper optimum. -/
theorem integerUpperDensity_le_smoothUpperOptimization {integral : Bool} {A : Set ℕ}
    (hA : IntegerPrefixAdmissible integral A) (Y : ℕ) :
    integerUpperDensity A ≤ integerSmoothUpperOptimization integral Y := by
  let T := integerRoughTemplateProducts (integerRoughNumbers Y) (integerSmoothPrefixJumps integral Y)
  have hd : HasNaturalDensity T (integerSmoothUpperOptimization integral Y) := by
    rw [integerSmoothUpperOptimization_eq_jump_reciprocal]
    exact hasNaturalDensity_integerRoughTemplateProducts Set.Subset.rfl
      (integerSmoothPrefixJumps_subset_smoothNumbers integral Y) (hasNaturalDensity_integerRoughNumbers Y)
  have hN (N : ℕ) : densityUpTo A N ≤ densityUpTo T N := by
    unfold densityUpTo
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast countUpTo_le_integerSmoothJumpProducts hA Y N) (Nat.cast_nonneg N)
  have hlim : Tendsto (densityUpTo T) atTop (𝓝 (integerSmoothUpperOptimization integral Y)) := hd
  exact (limsup_le_limsup (Eventually.of_forall hN)
    (isCoboundedUnder_le_of_le _ (densityUpTo_nonneg A)) hlim.isBoundedUnder_le).trans_eq hlim.limsup_eq

/-- The upper half `u ≤ U_Y` of the integer smooth-factor bound, for either
ratio convention and every cutoff. -/
theorem integerUpperDensitySupremum_le_smoothUpperOptimization (integral : Bool) (Y : ℕ) :
    integerUpperDensitySupremum integral ≤ integerSmoothUpperOptimization integral Y := by
  unfold integerUpperDensitySupremum
  apply csSup_le
  · refine ⟨integerUpperDensity ∅, ∅, by simp, ?_, rfl⟩
    intro a b c ha
    exact ha.elim
  · rintro d ⟨A, _, hA, rfl⟩
    exact integerUpperDensity_le_smoothUpperOptimization hA Y

end GRHArticle.ProgressionFree
