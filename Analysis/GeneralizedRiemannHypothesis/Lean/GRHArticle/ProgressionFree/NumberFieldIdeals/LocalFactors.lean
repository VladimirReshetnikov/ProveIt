import GRHArticle.ProgressionFree.NumberFieldIdeals.Density
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finite prime-ideal conditions

Removing multiples of a new prime ideal costs exactly the reciprocal
of its norm inside the set already coprime to a finite collection.
A further dilation then prescribes all the indicated exponents.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem HasNaturalDensity.sdiff {A B : Set (Ideal (𝓞 K))⁰} {a b : ℝ} (h : A ⊆ B)
    (ha : HasNaturalDensity A a) (hb : HasNaturalDensity B b) : HasNaturalDensity (B \ A) (b-a) := by
  apply (hb.sub ha).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
  let ball := {I : (Ideal (𝓞 K))⁰ | (absNorm I.val : ℝ) ≤ X}
  have hf : ball.Finite := (finite_setOf_absNorm_le₀ (S := 𝓞 K) ⌊X⌋₊).subset
    fun I hI ↦ (Nat.le_floor_iff hX).mpr hI
  have hdiff : (B \ A) ∩ ball = (B ∩ ball) \ (A ∩ ball) := by ext I; simp; tauto
  have he : (countUpTo (B \ A) X : ℝ) = (countUpTo B X : ℝ) - countUpTo A X := by
    change (((B \ A) ∩ ball).ncard : ℝ) = ((B ∩ ball).ncard : ℝ) - (A ∩ ball).ncard
    rw [hdiff]
    exact Set.cast_ncard_sdiff (Set.inter_subset_inter_left ball h) (hf.subset Set.inter_subset_right)
  simp only [densityUpTo, he, sub_div]

/-- A prime ideal as an element of the cancellative monoid of nonzero ideals. -/
def primeIdeal (p : HeightOneSpectrum (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩

/-- Nonzero integral ideals divisible by none of the specified primes. -/
def roughIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (Ideal (𝓞 K))⁰ :=
  {I | ∀ p ∈ S, ¬ primeIdeal p ∣ I}

private theorem primeIdeal_dvd_mul {p q : HeightOneSpectrum (𝓞 K)} (hne : p ≠ q)
    (I : (Ideal (𝓞 K))⁰) : primeIdeal p ∣ primeIdeal q * I ↔ primeIdeal p ∣ I := by
  simp only [nonZeroDivisors_dvd_iff_dvd_coe, Submonoid.coe_mul, primeIdeal]
  have hp := Ideal.prime_of_isPrime p.ne_bot p.isPrime
  have hq := Ideal.prime_of_isPrime q.ne_bot q.isPrime
  rw [hp.dvd_mul, hp.dvd_prime_iff_associated hq, associated_iff_eq]
  have hpq : p.asIdeal ≠ q.asIdeal := fun he ↦ hne (HeightOneSpectrum.ext he)
  simp [hpq]

theorem hasNaturalDensity_roughIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasNaturalDensity (roughIdeals S) (∏ p ∈ S, (1-(absNorm p.asIdeal : ℝ)⁻¹)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [roughIdeals] using (hasNaturalDensity_univ (K := K))
  | @insert p S hp ih =>
    let P := primeIdeal p
    have hrough (I : (Ideal (𝓞 K))⁰) : P * I ∈ roughIdeals S ↔ I ∈ roughIdeals S := by
      constructor <;> intro h q hq
      · exact fun hd ↦ h q hq ((primeIdeal_dvd_mul (p := q) (q := p) (fun he ↦ hp (he ▸ hq)) I).mpr hd)
      · exact fun hd ↦ h q hq ((primeIdeal_dvd_mul (p := q) (q := p) (fun he ↦ hp (he ▸ hq)) I).mp hd)
    have hsub : (P * ·) '' roughIdeals S ⊆ roughIdeals S := by
      rintro _ ⟨I,hI,rfl⟩
      exact (hrough I).mpr hI
    have heq : roughIdeals (insert p S) = roughIdeals S \ ((P * ·) '' roughIdeals S) := by
      ext I
      change (∀ q ∈ insert p S, ¬ primeIdeal q ∣ I) ↔ I ∈ roughIdeals S ∧ _
      rw [Finset.forall_mem_insert]
      constructor
      · rintro ⟨hn,hs⟩
        exact ⟨hs,fun ⟨J,_,he⟩ ↦ hn ⟨J,he.symm⟩⟩
      · rintro ⟨hs,hn⟩
        refine ⟨?_,hs⟩
        rintro ⟨J,rfl⟩
        exact hn ⟨J,(hrough J).mp hs,rfl⟩
    rw [heq,Finset.prod_insert hp]
    convert (ih.mul_image P).sdiff hsub ih using 1
    dsimp [P,primeIdeal]
    ring

/-- Prescribing the powers at finitely many prime ideals leaves their product
times an arbitrary rough ideal, of the indicated product density. -/
theorem hasNaturalDensity_exactPrimePowers (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K) → ℕ) :
    HasNaturalDensity (((∏ p ∈ S, primeIdeal p ^ v p) * ·) '' roughIdeals S)
      (∏ p ∈ S, ((1-(absNorm p.asIdeal : ℝ)⁻¹) * (absNorm p.asIdeal : ℝ)⁻¹ ^ v p)) := by
  have h := (hasNaturalDensity_roughIdeals S).mul_image (∏ p ∈ S, primeIdeal p ^ v p)
  simpa [Submonoid.coe_finsetProd, primeIdeal, div_eq_mul_inv, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib] using h

end GRHArticle.ProgressionFree.NumberFieldIdeals
