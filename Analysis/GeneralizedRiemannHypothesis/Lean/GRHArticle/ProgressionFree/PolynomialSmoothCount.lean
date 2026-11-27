import GRHArticle.ProgressionFree.PolynomialDegreeDensity
import GRHArticle.ProgressionFree.PolynomialRoughParts
import GRHArticle.ProgressionFree.PolynomialSmoothSeries

/-!
# Counting monic smooth polynomials by degree

Multiplying by a monic irreducible gives a bijection between the preceding
degree layer and the part of the current layer that contains that prime.
This identifies the finite geometric product with the actual counting series.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

/-- Monic degree-`n` polynomials whose normalized factors all belong to `S`. -/
noncomputable def polynomialSupportedLayer (S : Finset (Polynomial F)) (n : ℕ) :
    Finset (Polynomial F) :=
  (polynomialDegreeLayer F n).filter fun f ↦ f.Monic ∧ ∀ p ∈ normalizedFactors f, p ∈ S

theorem mem_polynomialSupportedLayer {S : Finset (Polynomial F)} {n : ℕ} {f : Polynomial F} :
    f ∈ polynomialSupportedLayer S n ↔
      f.Monic ∧ f.natDegree = n ∧ ∀ p ∈ normalizedFactors f, p ∈ S := by
  simp only [polynomialSupportedLayer, Finset.mem_filter, mem_polynomialDegreeLayer]
  exact ⟨fun h ↦ ⟨h.2.1, h.1.2, h.2.2⟩, fun h ↦ ⟨⟨h.1.ne_zero, h.2.1⟩, h.1, h.2.2⟩⟩

/-- The actual degree layer of monic polynomials with only degree-at-most-`L` primes. -/
noncomputable def polynomialSmoothLayer (F : Type*) [Field F] [Fintype F] (L n : ℕ) :
    Finset (Polynomial F) := polynomialSupportedLayer (polynomialSmoothPrimes F L) n

theorem mem_polynomialSmoothLayer {L n : ℕ} {f : Polynomial F} :
    f ∈ polynomialSmoothLayer F L n ↔
      f.Monic ∧ f.natDegree = n ∧ ∀ p ∈ normalizedFactors f, p.natDegree ≤ L := by
  rw [polynomialSmoothLayer, mem_polynomialSupportedLayer]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · exact fun h p hp ↦ (mem_polynomialSmoothPrimes.mp (h p hp)).2.2
  · intro h p hp
    have hi := irreducible_of_normalized_factor p hp
    exact mem_polynomialSmoothPrimes.mpr
      ⟨(normalize_eq_self_iff_monic hi.ne_zero).mp (normalize_normalized_factor p hp), hi, h p hp⟩

private theorem card_supported_empty (n : ℕ) :
    (polynomialSupportedLayer (∅ : Finset (Polynomial F)) n).card = if n = 0 then 1 else 0 := by
  have hempty (f : Polynomial F) :
      f ∈ polynomialSupportedLayer ∅ n ↔ f = 1 ∧ n = 0 := by
    rw [mem_polynomialSupportedLayer]
    constructor
    · rintro ⟨hm, hd, h⟩
      have he : normalizedFactors f = 0 := Multiset.eq_zero_of_forall_notMem (fun p hp ↦ Finset.notMem_empty _ (h p hp))
      have hf := Polynomial.leadingCoeff_mul_prod_normalizedFactors f
      rw [he, hm.leadingCoeff] at hf
      simp only [map_one, Multiset.prod_zero, mul_one] at hf
      exact ⟨hf.symm, by simpa [← hf] using hd.symm⟩
    · rintro ⟨rfl, rfl⟩
      simp
  split_ifs with hn
  · have he : polynomialSupportedLayer (∅ : Finset (Polynomial F)) n = {1} := by
      ext f
      rw [hempty]
      simp [hn]
    simp [he]
  · have he : polynomialSupportedLayer (∅ : Finset (Polynomial F)) n = ∅ := by
      ext f
      rw [hempty]
      simp [hn]
    simp [he]

omit [Fintype F] in
private theorem factors_mul_monic_prime {p g : Polynomial F}
    (hm : p.Monic) (hi : Irreducible p) (hg : g ≠ 0) :
    normalizedFactors (p * g) = p ::ₘ normalizedFactors g := by
  rw [normalizedFactors_mul hm.ne_zero hg, normalizedFactors_irreducible hi, hm.normalize_eq_self,
    Multiset.singleton_add]

private theorem card_supported_insert (S : Finset (Polynomial F)) {p : Polynomial F}
    (hp : p ∉ S) (hm : p.Monic) (hi : Irreducible p) (n : ℕ) :
    (polynomialSupportedLayer (insert p S) n).card = (polynomialSupportedLayer S n).card +
      if p.natDegree ≤ n then (polynomialSupportedLayer (insert p S) (n-p.natDegree)).card else 0 := by
  classical
  let A := polynomialSupportedLayer (insert p S) n
  have hfree : A.filter (fun f ↦ p ∉ normalizedFactors f) = polynomialSupportedLayer S n := by
    ext f
    simp only [A, Finset.mem_filter, mem_polynomialSupportedLayer]
    constructor
    · rintro ⟨⟨hf, hn, h⟩, hpf⟩
      exact ⟨hf, hn, fun z hz ↦ (Finset.mem_insert.mp (h z hz)).resolve_left (fun e ↦ hpf (e ▸ hz))⟩
    · rintro ⟨hf, hn, h⟩
      exact ⟨⟨hf, hn, fun z hz ↦ Finset.mem_insert_of_mem (h z hz)⟩, fun hpf ↦ hp (h p hpf)⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun f ↦ p ∈ normalizedFactors f)
  rw [hfree] at hsplit
  change A.card = _
  rw [← hsplit, add_comm]
  congr 1
  split_ifs with hd
  · let B := polynomialSupportedLayer (insert p S) (n - p.natDegree)
    have he : A.filter (fun f ↦ p ∈ normalizedFactors f) = B.image (p * ·) := by
      ext f
      simp only [A, B, Finset.mem_filter, mem_polynomialSupportedLayer, Finset.mem_image]
      constructor
      · rintro ⟨⟨hf, hn, h⟩, hpf⟩
        obtain ⟨g, rfl⟩ := dvd_of_mem_normalizedFactors hpf
        have hg : g ≠ 0 := (mul_ne_zero_iff.mp hf.ne_zero).2
        have hgmonic : g.Monic := by simpa [Monic, leadingCoeff_mul, hm.leadingCoeff] using hf.leadingCoeff
        have he := factors_mul_monic_prime hm hi hg
        refine ⟨g, ⟨hgmonic, ?_, fun z hz ↦ h z (he ▸ Multiset.mem_cons_of_mem hz)⟩, rfl⟩
        rw [natDegree_mul hm.ne_zero hg] at hn
        omega
      · rintro ⟨g, ⟨hgm, hgd, hgs⟩, rfl⟩
        rw [factors_mul_monic_prime hm hi hgm.ne_zero, natDegree_mul hm.ne_zero hgm.ne_zero]
        exact ⟨⟨hm.mul hgm, by omega, fun z hz ↦ (Multiset.mem_cons.mp hz).elim
          (fun e ↦ e ▸ Finset.mem_insert_self _ _) (hgs z)⟩, Multiset.mem_cons_self ..⟩
    rw [he, Finset.card_image_of_injective _ (mul_right_injective₀ hm.ne_zero)]
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨ha, hpf⟩ := Finset.mem_filter.mp hf
    obtain ⟨hf, hn, _⟩ := mem_polynomialSupportedLayer.mp ha
    exact hd (hn ▸ natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hpf) hf.ne_zero)

private theorem degreeGeometricSeries_unfold {d : ℕ} (hd : 0 < d) :
    degreeGeometricSeries d = 1 + PowerSeries.X ^ d * degreeGeometricSeries d := by
  ext n
  simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul', degreeGeometricSeries,
    PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn, hd.ne']
  · simp only [if_neg hn, zero_add]
    by_cases hle : d ≤ n
    · simp only [if_pos hle, Nat.dvd_sub_iff_left hle (dvd_refl d)]
    · rw [if_neg hle, if_neg (fun h ↦ hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h))]

/-- The coefficient of the finite product counts the actual supported monic polynomials. -/
theorem coeff_smoothDegreeCountingSeries_eq_card (S : Finset (Polynomial F))
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (n : ℕ) :
    PowerSeries.coeff n (smoothDegreeCountingSeries S Polynomial.natDegree) =
      (polynomialSupportedLayer S n).card := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty => simp [smoothDegreeCountingSeries, PowerSeries.coeff_one, card_supported_empty]
  | @insert p S hp ih =>
    obtain ⟨hm, hi⟩ := hS p (Finset.mem_insert_self _ _)
    have hd := hi.natDegree_pos
    have hs (q) (hq : q ∈ S) := hS q (Finset.mem_insert_of_mem hq)
    have he : smoothDegreeCountingSeries (insert p S) Polynomial.natDegree =
        smoothDegreeCountingSeries S Polynomial.natDegree +
        PowerSeries.X ^ p.natDegree * smoothDegreeCountingSeries (insert p S) Polynomial.natDegree := by
      simp only [smoothDegreeCountingSeries, Finset.prod_insert hp]
      nth_rw 1 [degreeGeometricSeries_unfold hd]
      rw [add_mul, one_mul, mul_assoc]
    induction n using Nat.strong_induction_on with
    | h n hn =>
      rw [he, map_add, PowerSeries.coeff_X_pow_mul', ih hs,
        card_supported_insert S hp hm hi]
      split_ifs with h
      · rw [hn _ (by omega)]
      · rfl

theorem coeff_polynomialSmoothDegreeSeries_eq_card (L n : ℕ) :
    PowerSeries.coeff n (polynomialSmoothDegreeSeries F L) = (polynomialSmoothLayer F L n).card :=
  coeff_smoothDegreeCountingSeries_eq_card (polynomialSmoothPrimes F L)
    (fun _ hp ↦ ⟨(mem_polynomialSmoothPrimes.mp hp).1, (mem_polynomialSmoothPrimes.mp hp).2.1⟩) n

/-- A whole rough class has positive signed gain at some deficit cutoff, measured in
actual monic smooth polynomials for each available degree. -/
theorem polynomialSmoothLayer_exists_positive_gain (L : ℕ) :
    ∃ R, 1 ≤ ∑ k ∈ Finset.range (R+1),
      ((polynomialSmoothLayer F L k).card : ℤ) * polynomialDeficitDifference (R-k) := by
  obtain ⟨R, hR⟩ := polynomialSmoothDegreeSeries_exists_positive_replacement_coefficient F L
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hR
  refine ⟨R, ?_⟩
  simpa only [PowerSeries.coeff_map, Nat.coe_castRingHom, PowerSeries.coeff_mk,
    coeff_polynomialSmoothDegreeSeries_eq_card] using hR

end GRHArticle.ProgressionFree
