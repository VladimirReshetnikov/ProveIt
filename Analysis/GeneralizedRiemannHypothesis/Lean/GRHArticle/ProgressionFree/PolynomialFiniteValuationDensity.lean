import GRHArticle.ProgressionFree.PolynomialFiniteValuationLaw
import GRHArticle.ProgressionFree.PolynomialGreedyCofactorDensity

/-!
# Finite valuation probabilities with or without a greedy exterior

Starting from the exact finite exclusion count gives the independent geometric
laws at a finite set of primes. Starting from the greedy cofactor limit gives
the same local series with the full greedy condition at the other primes.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- Require zero exponents in a finite set and a prescribed background elsewhere. -/
noncomputable def excludePrimeRules (S : Finset F[X]) (A : Set ℕ) (p : F[X]) : Set ℕ :=
  if p ∈ S then {0} else A

private theorem monicFamilyLayer_exclude_univ (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (n : ℕ) :
    monicFamilyLayer (monicValuationRuleSet (excludePrimeRules S Set.univ)) n =
      primeExcludingLayer S n := by
  ext f
  rw [mem_monicFamilyLayer, mem_primeExcludingLayer]
  refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h p hp
    exact (polynomialPrimeExponent_eq_zero_iff_not_dvd (hS p hp).1 (hS p hp).2 hm.ne_zero).mp
      (by simpa [excludePrimeRules, hp] using h.2 p)
  · intro h
    refine ⟨hm, fun p ↦ ?_⟩
    by_cases hp : p ∈ S
    · simpa [excludePrimeRules, hp] using
        (polynomialPrimeExponent_eq_zero_iff_not_dvd (hS p hp).1 (hS p hp).2 hm.ne_zero).mpr (h p hp)
    · simp [excludePrimeRules, hp]

/-- Independent local valuation probabilities with a finite disjoint list of
further excluded primes. Outside both finite sets there are no restrictions. -/
theorem tendsto_monicFamilyProportion_finiteValuations (S T : Finset F[X]) (D : F[X] → Set ℕ)
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (hT : ∀ p ∈ T, p.Monic ∧ Irreducible p)
    (hST : Disjoint S T) :
    Tendsto (monicFamilyProportion
      {f : F[X] | (∀ p ∈ S, ¬p ∣ f) ∧ ∀ p ∈ T, polynomialPrimeExponent p f ∈ D p}) atTop
      (𝓝 ((∏ p ∈ S, (1-(Fintype.card F : ℝ)⁻¹^p.natDegree)) *
        ∏ p ∈ T, ((1-(Fintype.card F : ℝ)⁻¹^p.natDegree) *
          primeExponentWeight ((Fintype.card F : ℝ)⁻¹^p.natDegree) (D p)))) := by
  let R := excludePrimeRules (S ∪ T) (Set.univ : Set ℕ)
  have hU (p) (hp : p ∈ S ∪ T) := (Finset.mem_union.mp hp).elim (hS p) (hT p)
  have hc : Tendsto (monicFamilyProportion (monicValuationRuleSet R)) atTop
      (𝓝 (∏ p ∈ S ∪ T, (1-(Fintype.card F : ℝ)⁻¹^p.natDegree))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (∑ p ∈ S ∪ T, p.natDegree)] with n hn
    dsimp only [monicFamilyProportion, R]
    rw [monicFamilyLayer_exclude_univ _ hU, normalized_primeExcludingLayer _ hU hn]
  have hlim := tendsto_monicValuationRuleSet_replace T R D hT
    (fun p hp ↦ by simp [R, excludePrimeRules, hp]) hc
  rw [Finset.prod_union hST, mul_assoc, ← Finset.prod_mul_distrib] at hlim
  refine hlim.congr (fun n ↦ ?_)
  unfold monicFamilyProportion
  apply congrArg (fun V : Finset F[X] ↦ (V.card : ℝ) / (Fintype.card F : ℝ)^n)
  ext f
  rw [mem_monicFamilyLayer, mem_monicFamilyLayer]
  refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h
    refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
    · have ht : p ∉ T := Finset.disjoint_left.mp hST hp
      exact (polynomialPrimeExponent_eq_zero_iff_not_dvd (hS p hp).1 (hS p hp).2 hm.ne_zero).mp
        (by simpa [replacePrimeRules, R, excludePrimeRules, hp, ht] using h.2 p)
    · simpa [replacePrimeRules, hp] using h.2 p
  · rintro ⟨hs, ht⟩
    refine ⟨hm, fun p ↦ ?_⟩
    by_cases hp : p ∈ T
    · simpa [replacePrimeRules, hp] using ht p hp
    · by_cases hp' : p ∈ S
      · simpa [replacePrimeRules, R, excludePrimeRules, hp, hp'] using
          (polynomialPrimeExponent_eq_zero_iff_not_dvd (hS p hp').1 (hS p hp').2 hm.ne_zero).mpr
            (hs p hp')
      · simp [replacePrimeRules, R, excludePrimeRules, hp, hp']

private theorem monicFamilyLayer_exclude_greedy (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (n : ℕ) :
    monicFamilyLayer (monicValuationRuleSet (excludePrimeRules S greedyExponents)) n =
      greedyPrimeAvoidingLayer S n := by
  ext f
  rw [mem_monicFamilyLayer, mem_greedyPrimeAvoidingLayer]
  refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h
    have hz (p : F[X]) (hp : p ∈ S) : polynomialPrimeExponent p f = 0 := by
      simpa [excludePrimeRules, hp] using h.2 p
    refine ⟨fun p hp ↦ (polynomialPrimeExponent_eq_zero_iff_not_dvd (hS p hp).1 (hS p hp).2
      hm.ne_zero).mp (hz p hp), fun p ↦ ?_⟩
    by_cases hp : p ∈ S
    · rw [hz p hp]; exact zero_mem_greedyExponents
    · simpa [excludePrimeRules, hp] using h.2 p
  · rintro ⟨hs, ht⟩
    refine ⟨hm, fun p ↦ ?_⟩
    by_cases hp : p ∈ S
    · simpa [excludePrimeRules, hp] using
        (polynomialPrimeExponent_eq_zero_iff_not_dvd (hS p hp).1 (hS p hp).2 hm.ne_zero).mpr (hs p hp)
    · simpa [excludePrimeRules, hp] using ht p

/-- Exact layer density for arbitrary coordinate rules at finitely many
primes and greedy exponents everywhere else. -/
theorem tendsto_monicValuationRuleSet_greedyExterior (S : Finset F[X]) (D : F[X] → Set ℕ)
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    Tendsto (monicFamilyProportion
      (monicValuationRuleSet (replacePrimeRules S (fun _ ↦ greedyExponents) D))) atTop
      (𝓝 (greedyPrimeAvoidingDensity S *
        ∏ p ∈ S, primeExponentWeight ((Fintype.card F : ℝ)⁻¹^p.natDegree) (D p))) := by
  let R := excludePrimeRules S greedyExponents
  have hc : Tendsto (monicFamilyProportion (monicValuationRuleSet R)) atTop
      (𝓝 (greedyPrimeAvoidingDensity S)) := by
    exact (tendsto_greedyPrimeAvoidingLayer_card_div_pow S hS).congr (fun n ↦ by
      simp only [monicFamilyProportion, R, monicFamilyLayer_exclude_greedy S hS])
  have he : replacePrimeRules S R D = replacePrimeRules S (fun _ ↦ greedyExponents) D := by
    funext p
    by_cases hp : p ∈ S <;> simp [replacePrimeRules, R, excludePrimeRules, hp]
  simpa only [he] using tendsto_monicValuationRuleSet_replace S R D hS
    (fun p hp ↦ by simp [R, excludePrimeRules, hp]) hc

end GRHArticle.ProgressionFree
