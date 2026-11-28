import GRHArticle.ProgressionFree.PolynomialIrreducibleLowerBound
import GRHArticle.ProgressionFree.PolynomialRoughCount
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Many distinct prime divisors of a random polynomial

Among degree-`n` monic polynomials, the probability of divisibility by each
of `t` fixed degree-`d` primes is at most `q^(-dt)`. Taking the union over
subsets gives the exceptional-layer estimate used in `gpp:thm:largeq`.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

/-- Multiples of a given monic polynomial on the monic degree layer. -/
noncomputable def monicMultipleLayer (f : F[X]) (n : ℕ) : Finset F[X] :=
  (monicLayer F n).filter (fun g ↦ f ∣ g)

theorem card_monicMultipleLayer_of_le {f : F[X]} (hf : f.Monic) {n : ℕ} (hn : f.natDegree ≤ n) :
    (monicMultipleLayer f n).card = Fintype.card F ^ (n-f.natDegree) := by
  rw [← card_monicLayer (F := F)]
  symm
  apply Finset.card_bij (fun g _ ↦ f*g)
  · intro g hg
    obtain ⟨hm, hd⟩ := mem_monicLayer.mp hg
    exact mem_filter.mpr ⟨mem_monicLayer.mpr ⟨hf.mul hm, by
      rw [natDegree_mul hf.ne_zero hm.ne_zero, hd, Nat.add_sub_of_le hn]⟩, dvd_mul_right f g⟩
  · exact fun _ _ _ _ he ↦ mul_left_cancel₀ hf.ne_zero he
  · intro g hg
    obtain ⟨hmem, a, rfl⟩ := mem_filter.mp hg
    obtain ⟨hm, hd⟩ := mem_monicLayer.mp hmem
    have ha := hf.of_mul_monic_left hm
    rw [natDegree_mul hf.ne_zero ha.ne_zero] at hd
    exact ⟨a, mem_monicLayer.mpr ⟨ha, by omega⟩, rfl⟩

theorem card_monicMultipleLayer_mul_pow_le {f : F[X]} (hf : f.Monic) (n : ℕ) :
    (monicMultipleLayer f n).card * Fintype.card F ^ f.natDegree ≤ Fintype.card F ^ n := by
  by_cases hn : f.natDegree ≤ n
  · rw [card_monicMultipleLayer_of_le hf hn, ← pow_add, Nat.sub_add_cancel hn]
  · have he : monicMultipleLayer f n = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro g hg
      obtain ⟨hg, hdiv⟩ := mem_filter.mp hg
      obtain ⟨hm, hd⟩ := mem_monicLayer.mp hg
      exact hn (hd ▸ natDegree_le_of_dvd hdiv hm.ne_zero)
    simp [he]

/-- Exact integer form of the union bound. The finite collection may be any
set of distinct monic irreducibles of the same degree, and `n` may be
smaller than the total requested divisor degree. -/
theorem card_monicLayer_many_divisors_mul_pow_le (S : Finset F[X]) (d n t : ℕ)
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p ∧ p.natDegree = d) :
    ((monicLayer F n).filter (fun g ↦ t ≤ (S.filter (· ∣ g)).card)).card *
      Fintype.card F ^ (d*t) ≤ S.card.choose t * Fintype.card F ^ n := by
  let U (A : Finset F[X]) := monicMultipleLayer (∏ p ∈ A, p) n
  have hsub : (monicLayer F n).filter (fun g ↦ t ≤ (S.filter (· ∣ g)).card) ⊆
      (S.powersetCard t).biUnion U := by
    intro g hg
    obtain ⟨hm, hmany⟩ := mem_filter.mp hg
    obtain ⟨A, hA, hsize⟩ := exists_subset_card_eq hmany
    have hAS : A ⊆ S := fun p hp ↦ (mem_filter.mp (hA hp)).1
    refine mem_biUnion.mpr ⟨A,mem_powersetCard.mpr ⟨hAS,hsize⟩,mem_filter.mpr ⟨hm,?_⟩⟩
    apply Finset.prod_dvd_of_isRelPrime _ (fun p hp ↦ (mem_filter.mp (hA hp)).2)
    intro p hp r hr hne
    obtain ⟨hpm, hpi, _⟩ := hS p (hAS hp)
    obtain ⟨hrm, hri, _⟩ := hS r (hAS hr)
    exact hpi.isRelPrime_iff_not_dvd.mpr fun hdiv ↦ hne
      (eq_of_monic_of_associated hpm hrm (hpi.associated_of_dvd hri hdiv))
  have hU (A : Finset F[X]) (hA : A ∈ S.powersetCard t) :
      (U A).card * Fintype.card F ^ (d*t) ≤ Fintype.card F ^ n := by
    obtain ⟨hAS,hsize⟩ := mem_powersetCard.mp hA
    have hm (p) (hp : p ∈ A) := (hS p (hAS hp)).1
    have he : (∏ p ∈ A, p).natDegree = d*t := by
      rw [natDegree_prod_of_monic _ _ hm, sum_congr rfl (fun p hp ↦ (hS p (hAS hp)).2.2)]
      simp [hsize, Nat.mul_comm]
    exact he ▸ card_monicMultipleLayer_mul_pow_le (monic_prod_of_monic _ _ hm) n
  calc
    _ ≤ (∑ A ∈ S.powersetCard t, (U A).card) * Fintype.card F ^ (d*t) :=
      Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ ≤ ∑ _A ∈ S.powersetCard t, Fintype.card F ^ n := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hU
    _ = _ := by simp

/-- The article's probability bound for the full set of monic degree-`d`
irreducibles. -/
theorem monicLayer_prime_divisor_tail (F : Type*) [Field F] [Fintype F] (d n t : ℕ) :
    let S := (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d)
    let E := (monicLayer F n).filter (fun g ↦ t ≤ (S.filter (· ∣ g)).card)
    (E.card : ℝ) / Fintype.card F ^ n ≤
      ((polynomialIrreducibleCount F d).choose t : ℝ) / Fintype.card F ^ (d*t) := by
  dsimp only
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  exact_mod_cast card_monicLayer_many_divisors_mul_pow_le _ d n t
    (fun p hp ↦ let h := mem_filter.mp hp
      let h' := mem_polynomialSmoothPrimes.mp h.1
      ⟨h'.1,h'.2.1,h.2⟩)

/-- Each nonzero scalar gives an identical degree layer for any condition
invariant under multiplication by that scalar. -/
theorem card_leadingCoeffLayer_eq_monic (u : Fˣ) (n : ℕ) (P : F[X] → Prop)
    (hP : ∀ g, P (C (u : F)*g) ↔ P g) :
    ((polynomialDegreeLayer F n).filter (fun f ↦ f.leadingCoeff = (u : F) ∧ P f)).card =
      ((monicLayer F n).filter P).card := by
  symm
  apply Finset.card_bij (fun g _ ↦ C (u : F)*g)
  · intro g hg
    obtain ⟨hg,hPg⟩ := mem_filter.mp hg
    obtain ⟨hm,hd⟩ := mem_monicLayer.mp hg
    refine mem_filter.mpr ⟨mem_polynomialDegreeLayer.mpr
      ⟨mul_ne_zero (C_ne_zero.mpr u.ne_zero) hm.ne_zero, (natDegree_C_mul u.ne_zero).trans hd⟩,
        ?_, (hP g).mpr hPg⟩
    simp [leadingCoeff_mul, hm.leadingCoeff]
  · exact fun _ _ _ _ he ↦ mul_left_cancel₀ (C_ne_zero.mpr u.ne_zero) he
  · intro f hf
    obtain ⟨hf,hl,hPf⟩ := mem_filter.mp hf
    obtain ⟨_,hd⟩ := mem_polynomialDegreeLayer.mp hf
    let g := C (↑u⁻¹ : F)*f
    have he : C (u : F)*g = f := by simp [g, ← mul_assoc, ← map_mul]
    refine ⟨g, mem_filter.mpr ⟨mem_monicLayer.mpr ⟨?_, (natDegree_C_mul u⁻¹.ne_zero).trans hd⟩,
      (hP g).mp (he ▸ hPf)⟩, he⟩
    change (C (↑u⁻¹ : F)*f).leadingCoeff = 1
    simp [leadingCoeff_mul,hl]

/-- Uniform exceptional-prime bound even after the leading coefficient
has been prescribed. This permits progression-free sets that distinguish
scalar multiples. -/
theorem leadingCoeffLayer_prime_divisor_tail (u : Fˣ) (d n t : ℕ) :
    let S := (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d)
    let E := (polynomialDegreeLayer F n).filter
      (fun g ↦ g.leadingCoeff = (u : F) ∧ t ≤ (S.filter (· ∣ g)).card)
    (E.card : ℝ) / Fintype.card F ^ n ≤
      ((polynomialIrreducibleCount F d).choose t : ℝ) / Fintype.card F ^ (d*t) := by
  let S := (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d)
  have he (g : F[X]) : S.filter (· ∣ (C (u : F)*g)) = S.filter (· ∣ g) := by
    have hu : IsUnit (C (u : F)) := u.isUnit.map C
    ext p
    simp [hu.dvd_mul_left]
  let P (g : F[X]) := t ≤ (S.filter (· ∣ g)).card
  let A := (polynomialDegreeLayer F n).filter (fun g ↦ g.leadingCoeff = (u : F) ∧ P g)
  let B := (monicLayer F n).filter P
  have hc := card_leadingCoeffLayer_eq_monic u n P (fun g ↦
    iff_of_eq (congrArg (fun a : Finset F[X] ↦ t ≤ a.card) (he g)))
  have hcard : A.card = B.card := by
    convert hc using 2 <;> ext x <;> simp [A,B]
  have hA : A = (polynomialDegreeLayer F n).filter
      (fun g ↦ g.leadingCoeff = (u : F) ∧ t ≤ (S.filter (· ∣ g)).card) := by
    ext g; simp [A,P]
  have hB : B = (monicLayer F n).filter (fun g ↦ t ≤ (S.filter (· ∣ g)).card) := by
    ext g; simp [B,P]
  rw [hA,hB] at hcard
  have h := monicLayer_prime_divisor_tail F d n t
  dsimp only at h ⊢
  convert h using 1
  rw [hcard]

end GRHArticle.ProgressionFree
