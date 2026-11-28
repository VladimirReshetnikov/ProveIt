import GRHArticle.ProgressionFree.PolynomialPrimePowerDensity
import GRHArticle.ProgressionFree.PolynomialPrimeDivisorTail
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Uniform tail for exterior valuation restrictions

An exponent rule that allows both zero and one can only fail at a prime
whose square divides the polynomial. The count of these square multiples
gives a geometric bound uniform in the degree layer.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The cofactor family avoiding `S` and satisfying the common rule at all primes. -/
def exteriorValuationCofactor (S : Finset F[X]) (D : Set ℕ) : Set F[X] :=
  {f | (∀ p ∈ S, ¬p ∣ f) ∧ (∀ p : F[X], polynomialPrimeExponent p f ∈ D)}

/-- The same cofactor rule tested only on a finite family of primes. -/
def finiteExteriorValuationCofactor (S T : Finset F[X]) (D : Set ℕ) : Set F[X] :=
  {f | (∀ p ∈ S, ¬p ∣ f) ∧ (∀ p ∈ T, polynomialPrimeExponent p f ∈ D)}

omit [Fintype F] in
private theorem pow_dvd_of_le_polynomialPrimeExponent {p f : F[X]}
    (hm : p.Monic) (hi : Irreducible p) (hf : f ≠ 0) {e : ℕ}
    (he : e ≤ polynomialPrimeExponent p f) : p^e ∣ f := by
  have hnorm : normalize p = p := (normalize_eq_self_iff_monic hi.ne_zero).mpr hm
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_count_normalizedFactors hi hf, hnorm]
  exact_mod_cast he

private theorem geometric_degreeTail_le {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) (L n : ℕ) :
    ∑ d ∈ Finset.Ioc L n, z^d ≤ z^(L+1)/(1-z) := by
  let a (d : ℕ) := if L < d then z^d else 0
  have ha : Summable a := by
    refine Summable.of_nonneg_of_le (fun d ↦ ?_) (fun d ↦ ?_)
      (summable_geometric_of_lt_one hz₀ hz₁)
    · by_cases hd : L < d <;> simp [a, hd, pow_nonneg hz₀]
    · by_cases hd : L < d <;> simp [a, hd, pow_nonneg hz₀]
  have htail : (∑' d, a d) = z^(L+1)/(1-z) := by
    rw [← ha.sum_add_tsum_nat_add (L+1)]
    have hzero : ∑ d ∈ Finset.range (L+1), a d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have h := Finset.mem_range.mp hd
      simp [a, show ¬L < d by omega]
    rw [hzero, zero_add]
    have hshift (d : ℕ) : a (d+(L+1)) = z^d*z^(L+1) := by
      simp [a, show L < d+(L+1) by omega, pow_add]
    simp_rw [hshift]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hz₀ hz₁, div_eq_mul_inv, mul_comm]
  rw [← htail]
  refine (Finset.sum_congr rfl (fun d hd ↦ ?_)).trans_le
    (ha.sum_le_tsum _ (fun d _ ↦ by by_cases hd : L < d <;> simp [a, hd, pow_nonneg hz₀]))
  exact (if_pos (Finset.mem_Ioc.mp hd).1).symm

private noncomputable def largeDegreePrimes (L n : ℕ) : Finset F[X] :=
  (polynomialSmoothPrimes F n).filter (fun p ↦ L < p.natDegree)

private theorem sum_largeDegreePrimeSquares_le (L n : ℕ) :
    let z := (Fintype.card F : ℝ)⁻¹
    ∑ p ∈ largeDegreePrimes (F := F) L n, z^(2*p.natDegree) ≤ z^(L+1)/(1-z) := by
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  let T := largeDegreePrimes (F := F) L n
  have hq : 1 < q := by dsimp [q]; exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hz₀ : 0 ≤ z := inv_nonneg.mpr hq₀.le
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  have hmap (p) (hp : p ∈ T) : p.natDegree ∈ Finset.Ioc L n := by
    obtain ⟨hp,hL⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨hL,(mem_polynomialSmoothPrimes.mp hp).2.2⟩
  change ∑ p ∈ T, z^(2*p.natDegree) ≤ _
  apply le_trans _ (geometric_degreeTail_le hz₀ hz₁ L n)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro d _
  let fiber := T.filter (fun p ↦ p.natDegree = d)
  have hcard : fiber.card ≤ Fintype.card F^d := by
    rw [← card_monicLayer (F := F)]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hT,he⟩ := Finset.mem_filter.mp hp
    have hp' := (Finset.mem_filter.mp hT).1
    exact mem_monicLayer.mpr ⟨(mem_polynomialSmoothPrimes.mp hp').1,he⟩
  have hcard' : (fiber.card : ℝ) ≤ q^d := by
    dsimp [q]
    exact_mod_cast hcard
  change ∑ p ∈ fiber, z^(2*p.natDegree) ≤ z^d
  calc
    _ = ∑ _p ∈ fiber, z^(2*d) := Finset.sum_congr rfl (fun p hp ↦ by rw [(Finset.mem_filter.mp hp).2])
    _ = (fiber.card : ℝ)*z^(2*d) := by simp
    _ ≤ q^d*z^(2*d) := mul_le_mul_of_nonneg_right hcard' (pow_nonneg hz₀ _)
    _ = z^d := by
      rw [two_mul, pow_add, ← mul_assoc]
      have hcancel : q^d*z^d = 1 := by
        rw [show z = q⁻¹ by rfl, ← mul_pow, mul_inv_cancel₀ hq₀.ne', one_pow]
      rw [hcancel, one_mul]

/-- Admitting all omitted valuations changes the normalized count by at most
the geometric tail from primes of degree greater than `L`. -/
theorem finiteExteriorValuationCofactor_tail
    (S T : Finset F[X]) (D : Set ℕ) (h₀ : 0 ∈ D) (h₁ : 1 ∈ D) (L n : ℕ)
    (hcover : ∀ p ∈ polynomialSmoothPrimes F L, p ∉ S → p ∈ T) :
    let z := (Fintype.card F : ℝ)⁻¹
    monicFamilyProportion (exteriorValuationCofactor S D) n ≤
      monicFamilyProportion (finiteExteriorValuationCofactor S T D) n ∧
    monicFamilyProportion (finiteExteriorValuationCofactor S T D) n ≤
      monicFamilyProportion (exteriorValuationCofactor S D) n + z^(L+1)/(1-z) := by
  let A := monicFamilyLayer (exteriorValuationCofactor S D) n
  let B := monicFamilyLayer (finiteExteriorValuationCofactor S T D) n
  let U := largeDegreePrimes (F := F) L n
  let E := U.biUnion fun p ↦ monicMultipleLayer (p^2) n
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hA : A ⊆ B := by
    intro f hf
    obtain ⟨hm,hd,hs,ha⟩ := mem_monicFamilyLayer.mp hf
    exact mem_monicFamilyLayer.mpr ⟨hm,hd,hs,fun p _ ↦ ha p⟩
  have hB : B ⊆ A ∪ E := by
    intro f hf
    by_cases h : f ∈ A
    · exact Finset.mem_union_left _ h
    · obtain ⟨hm,hd,hs,ht⟩ := mem_monicFamilyLayer.mp hf
      have hfail : ¬∀ p : F[X], polynomialPrimeExponent p f ∈ D := fun hp ↦
        h (mem_monicFamilyLayer.mpr ⟨hm,hd,hs,hp⟩)
      obtain ⟨p,hp⟩ := not_forall.mp hfail
      have hlarge : 2 ≤ polynomialPrimeExponent p f := by
        by_contra! hsmall
        have he : polynomialPrimeExponent p f = 0 ∨ polynomialPrimeExponent p f = 1 := by omega
        exact hp (he.elim (fun h ↦ h.symm ▸ h₀) (fun h ↦ h.symm ▸ h₁))
      have hpF : p ∈ normalizedFactors f := Multiset.count_ne_zero.mp (by
        change polynomialPrimeExponent p f ≠ 0
        omega)
      obtain ⟨hpi,hpm,hpf⟩ := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp hpF
      have hpS : p ∉ S := fun h ↦ hs p h hpf
      have hpn : p.natDegree ≤ n := hd ▸ natDegree_le_of_dvd hpf hm.ne_zero
      have hpL : L < p.natDegree := by
        by_contra! hle
        exact hp (ht p (hcover p (mem_polynomialSmoothPrimes.mpr ⟨hpm,hpi,hle⟩) hpS))
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,?_,?_⟩)
      · exact Finset.mem_filter.mpr ⟨mem_polynomialSmoothPrimes.mpr ⟨hpm,hpi,hpn⟩, hpL⟩
      · exact Finset.mem_filter.mpr ⟨mem_monicLayer.mpr ⟨hm,hd⟩,
          pow_dvd_of_le_polynomialPrimeExponent hpm hpi hm.ne_zero hlarge⟩
  have hEs (p : F[X]) (hp : p ∈ U) :
      ((monicMultipleLayer (p^2) n).card : ℝ) / q^n ≤ z^(2*p.natDegree) := by
    have hpm := (mem_polynomialSmoothPrimes.mp (Finset.mem_filter.mp hp).1).1
    have h := card_monicMultipleLayer_mul_pow_le (hpm.pow 2) n
    have he : (p^2).natDegree = 2*p.natDegree := by rw [natDegree_pow]
    rw [he] at h
    have h' : ((monicMultipleLayer (p^2) n).card : ℝ) * q^(2*p.natDegree) ≤ q^n := by
      dsimp [q]
      exact_mod_cast h
    rw [show z = q⁻¹ by rfl, inv_pow, inv_eq_one_div]
    exact (div_le_div_iff₀ (pow_pos hq _) (pow_pos hq _)).mpr (by simpa using h')
  have hE : (E.card : ℝ)/q^n ≤ z^(L+1)/(1-z) := by
    calc
      _ ≤ ((∑ p ∈ U, (monicMultipleLayer (p^2) n).card : ℕ):ℝ)/q^n := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hq.le _)
        exact_mod_cast (Finset.card_biUnion_le : E.card ≤ _)
      _ = ∑ p ∈ U, ((monicMultipleLayer (p^2) n).card : ℝ)/q^n := by
        simp only [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ ∑ p ∈ U, z^(2*p.natDegree) := Finset.sum_le_sum hEs
      _ ≤ _ := sum_largeDegreePrimeSquares_le (F := F) L n
  change (A.card : ℝ)/q^n ≤ (B.card : ℝ)/q^n ∧
    (B.card : ℝ)/q^n ≤ (A.card : ℝ)/q^n + z^(L+1)/(1-z)
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hA) (pow_nonneg hq.le _)
  · have hc : B.card ≤ A.card + E.card :=
      (Finset.card_le_card hB).trans (Finset.card_union_le _ _)
    calc
      _ ≤ ((A.card : ℝ)+(E.card : ℝ))/q^n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg hq.le _)
      _ = (A.card : ℝ)/q^n + (E.card : ℝ)/q^n := add_div _ _ _
      _ ≤ _ := add_le_add_right hE _

end GRHArticle.ProgressionFree
