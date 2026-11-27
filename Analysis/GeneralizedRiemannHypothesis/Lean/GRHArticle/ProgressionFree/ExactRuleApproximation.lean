import GRHArticle.ProgressionFree.ExactPatternDensity
import GRHArticle.ProgressionFree.ExchangeApproximation

/-!
# Natural density of a correlated exact-valuation rule

An arbitrary rule on the affected primes is compatible with a uniform
approximation by bounded exponents. The contribution of omitted primes is
controlled because the greedy rule admits exponents zero and one.
-/

open Filter
open scoped BigOperators Topology

namespace GRHArticle.ProgressionFree

/-- A rule on the exact affected exponents, with all other prime exponents
still following Rankin's rule. -/
def exactValuationRuleSet (marker : ℕ) (S : Finset ℕ) (C : Set (ℕ × (↥S → ℕ))) : Set ℕ :=
  {n | n ≠ 0 ∧ (n.factorization marker, fun i : ↥S => n.factorization i.val) ∈ C ∧
    ∀ p : ℕ, p.Prime → p ≠ marker → p ∉ S → n.factorization p ∈ greedyExponents}

/-- The unmodified Rankin patterns across the affected coordinates. -/
def rankinExactExponentSet (ι : Type*) : Set (ℕ × (ι → ℕ)) :=
  {v | v.1 ∈ greedyExponents ∧ ∀ i, v.2 i ∈ greedyExponents}

theorem exactValuationRuleSet_rankin {marker : ℕ} {S : Finset ℕ}
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) :
    exactValuationRuleSet marker S (rankinExactExponentSet ↥S) = rankinSet := by
  ext n
  constructor
  · rintro ⟨hn, hC, hrest⟩
    refine ⟨hn, fun p hp => ?_⟩
    by_cases hpm : p = marker
    · subst p
      exact hC.1
    · by_cases hps : p ∈ S
      · exact hC.2 ⟨p, hps⟩
      · exact hrest p hp hpm hps
  · rintro ⟨hn, h⟩
    exact ⟨hn, ⟨h marker hm, fun p => h p.val (hS p.val p.property)⟩, fun p hp _ _ => h p hp⟩

private theorem not_greedy_implies_square_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (h : n.factorization p ∉ greedyExponents) : p ^ 2 ∣ n := by
  apply (hp.pow_dvd_iff_le_factorization hn).mpr
  by_contra hh
  have hz : n.factorization p = 0 ∨ n.factorization p = 1 := by omega
  rcases hz with hz | hz
  · exact h (hz.symm ▸ zero_mem_greedyExponents)
  · exact h (hz.symm ▸ one_mem_greedyExponents)

private theorem exactRule_error_event {marker Y K : ℕ} {S : Finset ℕ}
    (C : Set (ℕ × (↥S → ℕ))) (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime)
    (hmY : marker ≤ Y) (hSY : ∀ p ∈ S, p ≤ Y) :
    let T := finiteExactRuleSet (exchangeAffected marker S)
      (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C K
    (exactValuationRuleSet marker S C \ T) ∪ (T \ exactValuationRuleSet marker S C) ⊆
      {n | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p ^ 2 ∣ n} ∪ {n | ∃ p ∈ Nat.primesLE Y, p ^ K ∣ n} := by
  intro T n hn
  rcases hn with h | h
  · obtain ⟨hd, ht⟩ := h
    apply Or.inr
    by_contra hlarge
    have hsmall (p : ℕ) (hp : p ∈ Nat.primesLE Y) : n.factorization p < K := by
      by_contra hp'
      exact hlarge ⟨p, hp, ((Nat.prime_of_mem_primesLE hp).pow_dvd_iff_le_factorization hd.1).mpr
        (Nat.le_of_not_gt hp')⟩
    apply ht
    refine ⟨hd.1, mem_boundedExactPatterns.mpr ⟨hd.2.1, ?_, ?_⟩, ?_⟩
    · exact hsmall marker (Nat.mem_primesLE.mpr ⟨hmY, hm⟩)
    · intro i
      exact hsmall i.val (Nat.mem_primesLE.mpr ⟨hSY i.val i.property, hS i.val i.property⟩)
    · intro q
      have hq := Finset.mem_sdiff.mp q.property
      have hm' : q.val ≠ marker := fun h => hq.2 (Finset.mem_insert.mpr (Or.inl h))
      have hS' : q.val ∉ S := fun h => hq.2 (Finset.mem_insert.mpr (Or.inr h))
      exact mem_greedyExponentsBelow.mpr
        ⟨hd.2.2 _ (exchangeRough_prime q) hm' hS', hsmall _ hq.1⟩
  · obtain ⟨ht, hd⟩ := h
    apply Or.inl
    by_contra hlarge
    apply hd
    refine ⟨ht.1, (mem_boundedExactPatterns.mp ht.2.1).1, fun p hp hpm hpS => ?_⟩
    by_cases hle : p ≤ Y
    · have hmem : p ∈ exchangeRough marker S Y := Finset.mem_sdiff.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hle, hp⟩, fun h => (Finset.mem_insert.mp h).elim hpm hpS⟩
      exact (mem_greedyExponentsBelow.mp (ht.2.2 ⟨p, hmem⟩)).1
    · by_contra hnot
      exact hlarge ⟨p, lt_of_not_ge hle, hp, not_greedy_implies_square_dvd ht.1 hp hnot⟩

/-- Uniform counting error for the exact-rule truncation. -/
theorem abs_densityUpTo_exactRule_sub_trunc_le {marker Y K : ℕ} {S : Finset ℕ}
    (C : Set (ℕ × (↥S → ℕ))) (N : ℕ) (hm : marker.Prime)
    (hS : ∀ p ∈ S, p.Prime) (hmY : marker ≤ Y) (hSY : ∀ p ∈ S, p ≤ Y) (hY : 0 < Y) :
    |densityUpTo (exactValuationRuleSet marker S C) N - densityUpTo (finiteExactRuleSet
      (exchangeAffected marker S) (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C K) N| ≤
      1 / (Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ K := by
  let E := {n : ℕ | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p ^ 2 ∣ n}
  let F := {n : ℕ | ∃ p ∈ Nat.primesLE Y, p ^ K ∣ n}
  calc
    _ ≤ densityUpTo (E ∪ F) N := densityUpTo_abs_sub_le_of_symmDiff_subset N
      (exactRule_error_event C hm hS hmY hSY)
    _ ≤ densityUpTo E N + densityUpTo F N := densityUpTo_union_le E F N
    _ ≤ _ := by
      apply add_le_add (densityUpTo_largePrimeSquare_le Y N hY)
      simpa only [F, Nat.cast_pow] using
        densityUpTo_divisibleByOneOf_le (Nat.primesLE Y) (fun p => p ^ K) N
          (fun p hp => pow_pos (Nat.prime_of_mem_primesLE hp).pos _)

theorem exists_hasNaturalDensity_exactValuationRuleSet {marker : ℕ} {S : Finset ℕ}
    (C : Set (ℕ × (↥S → ℕ))) (hm : marker.Prime)
    (hS : ∀ p ∈ S, p.Prime) (hdisj : marker ∉ S) :
    ∃ d, HasNaturalDensity (exactValuationRuleSet marker S C) d := by
  apply exists_hasNaturalDensity_of_uniform_approximation
  intro ε hε
  obtain ⟨Y, L, hY, _, hmY, hSY, hbound⟩ := exists_digitRule_cutoffs marker S hε
  refine ⟨_, _, hasNaturalDensity_finiteExactRuleSet (exchangeAffected marker S)
    (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C (3 * L)
    (exchangePrimeCoordinates_injective hdisj) (exchangeAffected_prime hm hS) exchangeRough_prime, ?_⟩
  intro N
  exact (abs_densityUpTo_exactRule_sub_trunc_le C N hm hS hmY hSY hY).trans hbound

end GRHArticle.ProgressionFree
