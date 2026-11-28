import GRHArticle.ProgressionFree.PolynomialPrimePowerDensity

/-!
# Finite changes to local exponent rules

Starting with a family that excludes finitely many monic irreducibles,
allow an arbitrary set of exponents at each of them. Its density is the
old monic degree-layer density times the product of the local series.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F]

/-- Monic polynomials satisfying each of a family of exponent rules. -/
def monicValuationRuleSet (R : F[X] → Set ℕ) : Set F[X] :=
  {f | f.Monic ∧ ∀ p, polynomialPrimeExponent p f ∈ R p}

/-- Override a background exponent rule on a finite set. -/
noncomputable def replacePrimeRules (S : Finset F[X]) (R D : F[X] → Set ℕ) (p : F[X]) :
    Set ℕ := if p ∈ S then D p else R p

theorem polynomialPrimeExponent_eq_zero_iff_not_dvd {P g : F[X]} (hP : P.Monic)
    (hi : Irreducible P) (hg : g ≠ 0) : polynomialPrimeExponent P g = 0 ↔ ¬P ∣ g := by
  simp only [polynomialPrimeExponent, Multiset.count_eq_zero,
    Polynomial.mem_normalizedFactors_iff hg, hi, hP, true_and]

private theorem polynomialPrimeExponent_mul_prime_pow (p : F[X]) {g P : F[X]}
    (hg : g.Monic) (hm : P.Monic) (hi : Irreducible P) (e : ℕ) :
    polynomialPrimeExponent p (g*P^e) =
      polynomialPrimeExponent p g + if p = P then e else 0 := by
  rw [polynomialPrimeExponent_mul p hg.ne_zero (pow_ne_zero _ hi.ne_zero)]
  simp [polynomialPrimeExponent, hi.normalizedFactors_pow, hm.normalize_eq_self,
    Multiset.count_replicate, eq_comm]

theorem monicValuationRuleSet_replace_single {P : F[X]} (hP : P.Monic) (hi : Irreducible P)
    (R : F[X] → Set ℕ) (D : Set ℕ) (hR : R P = {0}) :
    monicValuationRuleSet (fun p ↦ if p = P then D else R p) =
      extendByPrimePowers P D (monicValuationRuleSet R) := by
  ext f
  constructor
  · rintro ⟨hm, hf⟩
    let g := oneFreePrimeCofactor P f
    have hg := monic_oneFreePrimeCofactor P f
    refine ⟨g, ⟨hg, ?_⟩, polynomialPrimeExponent P f, ?_, ?_⟩
    · intro p
      by_cases he : p = P
      · subst p; simp [g, polynomialPrimeExponent_oneFreePrimeCofactor, hR]
      · simpa only [g, polynomialPrimeExponent_oneFreePrimeCofactor, if_neg he] using
          (show polynomialPrimeExponent p f ∈ (if p = P then D else R p) from hf p)
    · simpa using hf P
    · simpa only [hm.leadingCoeff, C_1, one_mul, g] using
        (polynomial_eq_scalar_mul_oneFreePrimeCofactor_mul_pow P f).symm
  · rintro ⟨g, ⟨hg, hgr⟩, e, he, rfl⟩
    refine ⟨hg.mul (hP.pow e), fun p ↦ ?_⟩
    rw [polynomialPrimeExponent_mul_prime_pow p hg hP hi]
    by_cases hp : p = P
    · subst p
      have hz := hgr P
      rw [hR, Set.mem_singleton_iff] at hz
      simpa [hz] using he
    · simpa [hp] using hgr p

variable [Fintype F]

/-- The finite product law for arbitrary local rules on the selected primes
and a fixed background exponent rule elsewhere. -/
theorem tendsto_monicValuationRuleSet_replace (S : Finset F[X]) (R D : F[X] → Set ℕ)
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (hR : ∀ p ∈ S, R p = {0})
    {c : ℝ} (hc : Tendsto (monicFamilyProportion (monicValuationRuleSet R)) atTop (𝓝 c)) :
    Tendsto (monicFamilyProportion (monicValuationRuleSet (replacePrimeRules S R D))) atTop
      (𝓝 (c * ∏ p ∈ S, primeExponentWeight ((Fintype.card F : ℝ)⁻¹^p.natDegree) (D p))) := by
  induction S using Finset.induction_on with
  | empty =>
    have he : replacePrimeRules (∅ : Finset F[X]) R D = R := by ext p; simp [replacePrimeRules]
    simpa only [he, Finset.prod_empty, mul_one] using hc
  | @insert P S hP ih =>
    have hp := hS P (Finset.mem_insert_self ..)
    let R' := replacePrimeRules S R D
    have hzero : R' P = {0} := by simp [R', replacePrimeRules, hP, hR P (Finset.mem_insert_self ..)]
    have hset : monicValuationRuleSet (replacePrimeRules (insert P S) R D) =
        extendByPrimePowers P (D P) (monicValuationRuleSet R') := by
      rw [← monicValuationRuleSet_replace_single hp.1 hp.2 R' (D P) hzero]
      congr 1
      funext p
      by_cases he : p = P <;> simp [replacePrimeRules, R', he]
    rw [hset, Finset.prod_insert hP]
    have hl := ih (fun p h ↦ hS p (Finset.mem_insert_of_mem h))
      (fun p h ↦ hR p (Finset.mem_insert_of_mem h))
    have ht := tendsto_monicFamilyProportion_extendByPrimePowers hp.1 hp.2 (D P)
      (B := monicValuationRuleSet R') (fun g hg ↦ ⟨hg.1,
        (polynomialPrimeExponent_eq_zero_iff_not_dvd hp.1 hp.2 hg.1.ne_zero).mp
          (by simpa [hzero] using hg.2 P)⟩) hl
    simpa only [mul_right_comm, mul_assoc, mul_left_comm] using ht

end GRHArticle.ProgressionFree
