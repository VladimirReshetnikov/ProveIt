import GRHArticle.ProgressionFree.Rankin
import GRHArticle.ProgressionFree.Density

/-!
# Finite approximations to Rankin's set
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- The admissible Rankin exponents strictly below a finite cutoff. -/
noncomputable def greedyExponentsBelow (L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range L).filter (· ∈ greedyExponents)

theorem mem_greedyExponentsBelow {L e : ℕ} :
    e ∈ greedyExponentsBelow L ↔ e ∈ greedyExponents ∧ e < L := by
  classical
  simp only [greedyExponentsBelow, Finset.mem_filter, Finset.mem_range, and_comm]

/-- Impose Rankin's exponent rule at a finite collection of primes and retain
only exponents below `L` at those primes. -/
def rankinFiniteTruncation (S : Finset ℕ) (L : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p ∈ S, n.factorization p ∈ greedyExponents ∧ n.factorization p < L}

/-- Exact natural density of the finite-prime, bounded-exponent Rankin
truncation. -/
theorem hasNaturalDensity_rankinFiniteTruncation (S : Finset ℕ) (L : ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    HasNaturalDensity (rankinFiniteTruncation S L)
      (∏ p : ↥S, (1 - 1 / (p.val : ℝ)) *
        ∑ e ∈ greedyExponentsBelow L, (1 / (p.val : ℝ)) ^ e) := by
  have hset : rankinFiniteTruncation S L =
      {n | n ≠ 0 ∧ ∀ p : ↥S, n.factorization p.val ∈ greedyExponentsBelow L} := by
    ext n
    constructor
    · intro h
      exact ⟨h.1, fun p => mem_greedyExponentsBelow.mpr (h.2 p.val p.property)⟩
    · intro h
      exact ⟨h.1, fun p hp => mem_greedyExponentsBelow.mp (h.2 ⟨p, hp⟩)⟩
  rw [hset]
  exact hasNaturalDensity_finite_prime_rules S (fun _ => greedyExponentsBelow L) hS

/-- The truncation can disagree with Rankin's set only when an omitted prime
square divides the integer or a tracked exponent reaches the cutoff. -/
theorem rankinSet_symmDiff_rankinFiniteTruncation_subset (S : Finset ℕ) (L : ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (rankinSet \ rankinFiniteTruncation S L) ∪ (rankinFiniteTruncation S L \ rankinSet) ⊆
      {n | (∃ p : ℕ, p.Prime ∧ p ∉ S ∧ p ^ 2 ∣ n) ∨ ∃ p ∈ S, p ^ L ∣ n} := by
  intro n hn
  rcases hn with h | h
  · obtain ⟨hr, ht⟩ := h
    have hlarge : ¬ ∀ p ∈ S, n.factorization p < L := by
      intro hlt
      exact ht ⟨hr.1, fun p hp => ⟨hr.2 p (hS p hp), hlt p hp⟩⟩
    push Not at hlarge
    obtain ⟨p, hp, hLp⟩ := hlarge
    exact Or.inr ⟨p, hp, ((hS p hp).pow_dvd_iff_le_factorization hr.1).mpr hLp⟩
  · obtain ⟨ht, hr⟩ := h
    have hbad : ¬ ∀ p : ℕ, p.Prime → n.factorization p ∈ greedyExponents :=
      fun hp => hr ⟨ht.1, hp⟩
    push Not at hbad
    obtain ⟨p, hp, hg⟩ := hbad
    have hnotmem : p ∉ S := fun hs => hg (ht.2 p hs).1
    have htwo : 2 ≤ n.factorization p := by
      by_contra hlt
      have hsmall : n.factorization p = 0 ∨ n.factorization p = 1 := by omega
      apply hg
      rcases hsmall with h₀ | h₁
      · rw [h₀]
        exact zero_mem_greedyExponents
      · rw [h₁]
        exact one_mem_greedyExponents
    exact Or.inl ⟨p, hp, hnotmem, (hp.pow_dvd_iff_le_factorization ht.1).mpr htwo⟩

end GRHArticle.ProgressionFree
