import GRHArticle.ProgressionFree.NumberFieldIdeals.LocalFactors

/-!
# Joint geometric law for finitely many prime-ideal exponents

An exponent is exactly `e` precisely when the `e`-th power of the prime
divides the ideal and the next power does not. This description makes
each event independent of the choice of a factorization function.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem not_dvd_other {p q : HeightOneSpectrum (𝓞 K)} (h : p ≠ q) :
    ¬ p.asIdeal ∣ q.asIdeal := by
  rw [(Ideal.prime_of_isPrime p.ne_bot p.isPrime).dvd_prime_iff_associated
    (Ideal.prime_of_isPrime q.ne_bot q.isPrime), associated_iff_eq]
  exact fun he ↦ h (HeightOneSpectrum.ext he)

private theorem mem_powers_mul_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K) → ℕ) (I : (Ideal (𝓞 K))⁰) :
    I ∈ ((∏ p ∈ S, primeIdeal p ^ v p) * ·) '' roughIdeals S ↔
      ∀ p ∈ S, p.asIdeal ^ v p ∣ I.val ∧ ¬ p.asIdeal ^ (v p+1) ∣ I.val := by
  classical
  let D := ∏ p ∈ S, primeIdeal p ^ v p
  have hD : D.val = ∏ p ∈ S, p.asIdeal ^ v p := by
    simp [D,primeIdeal]
  have hcut (p) (hp : p ∈ S) (J : (Ideal (𝓞 K))⁰) :
      p.asIdeal^(v p+1) ∣ (D*J).val ↔ primeIdeal p ∣ J := by
    let L := ∏ q ∈ S.erase p, q.asIdeal ^ v q
    have hp' := Ideal.prime_of_isPrime p.ne_bot p.isPrime
    have hL : ¬p.asIdeal ∣ L := by
      intro hc
      obtain ⟨q,hq,hdiv⟩ := hp'.exists_mem_finset_dvd hc
      exact not_dvd_other (mem_erase.mp hq).1.symm (hp'.dvd_of_dvd_pow hdiv)
    have he : D.val = p.asIdeal ^ v p * L := hD.trans (mul_prod_erase S (fun q ↦ q.asIdeal^v q) hp).symm
    rw [Submonoid.coe_mul, he, mul_assoc, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp'.ne_zero),
      hp'.dvd_mul, or_iff_right hL, nonZeroDivisors_dvd_iff_dvd_coe]
    rfl
  constructor
  · rintro ⟨J,hJ,rfl⟩ p hp
    refine ⟨?_,fun hh ↦ hJ p hp ((hcut p hp J).mp hh)⟩
    change p.asIdeal^v p ∣ D.val * J.val
    apply dvd_mul_of_dvd_left _ _
    rw [hD]
    exact dvd_prod_of_mem _ hp
  · intro hI
    have hd : D ∣ I := by
      rw [nonZeroDivisors_dvd_iff_dvd_coe,hD]
      apply Finset.prod_dvd_of_isRelPrime _ (fun p hp ↦ (hI p hp).1)
      intro p _ q _ hpq
      exact (((Ideal.prime_of_isPrime p.ne_bot p.isPrime).irreducible.isRelPrime_iff_not_dvd.mpr
        (not_dvd_other hpq)).pow_left).pow_right
    obtain ⟨J,rfl⟩ := hd
    refine ⟨J,?_,rfl⟩
    intro p hp hh
    exact (hI p hp).2 ((hcut p hp J).mpr hh)

/-- The prime-ideal valuation events have independent geometric densities,
the finite-cylinder formula used in the article's product-set lemma. -/
theorem hasNaturalDensity_valuationCylinder (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K) → ℕ) :
    HasNaturalDensity {I : (Ideal (𝓞 K))⁰ | ∀ p ∈ S,
        p.asIdeal ^ v p ∣ I.val ∧ ¬ p.asIdeal ^ (v p+1) ∣ I.val}
      (∏ p ∈ S, ((1-(absNorm p.asIdeal : ℝ)⁻¹) * (absNorm p.asIdeal : ℝ)⁻¹ ^ v p)) := by
  convert hasNaturalDensity_exactPrimePowers S v using 1
  exact Set.ext fun I ↦ (mem_powers_mul_iff S v I).symm

end GRHArticle.ProgressionFree.NumberFieldIdeals
