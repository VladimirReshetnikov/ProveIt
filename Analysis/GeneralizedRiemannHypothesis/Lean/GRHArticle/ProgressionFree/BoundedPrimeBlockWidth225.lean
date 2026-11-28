import GRHArticle.ProgressionFree.FourMarkerDensity
import GRHArticle.ProgressionFree.IntegerSharedDeletion
import GRHArticle.ProgressionFree.WidthPreservingFiniteExceptions

/-!
# An improving block of width 225

The four-marker rule is one exceptional block on the primes up to 1427.
The same rule gives a lower bound for the width-225 extremum.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical

private theorem kTermGPFree_three_of_threeGPFree {A : Set ℕ} (hA : ThreeGPFree A) :
    KTermGPFree 3 A := by
  intro a u r hu hr hm he
  have h₀ : (a 0 : ℚ) = u := by simpa using he 0
  have h₁ : (a 1 : ℚ) = u*r := by simpa using he 1
  have h₂ : (a 2 : ℚ) = u*r^2 := by simpa using he 2
  have hprod : a 0 * a 2 = a 1 * a 1 := by
    suffices h : (a 0 : ℚ) * (a 2 : ℚ) = (a 1 : ℚ) * (a 1 : ℚ) by exact_mod_cast h
    rw [h₀,h₁,h₂]
    ring
  have heq := hA (hm 0) (hm 1) (hm 2) hprod
  have h : u * r = u * 1 := by
    rw [← h₁,mul_one,← h₀]
    exact_mod_cast heq.symm
  exact mul_left_cancel₀ hu.ne' h

/-- The marker prime and the satellites can be coupled into a single block. -/
theorem integerBoundedPrimeBlockSet_fourMarkerExchange (S : Finset ℕ) {d : ℕ}
    (hd : 0 < d) (hPr : ∀ p ∈ S, p.Prime) (hCard : (insert 2 S).card ≤ d) :
    IntegerBoundedPrimeBlockSet d (fourMarkerExchangeSet S) := by
  let P := insert 2 S
  have h₂ : 2 ∈ P := mem_insert_self 2 S
  have hSat (p : ↥S) : p.val ∈ P := mem_insert_of_mem p.property
  let F : Set (↥P → ℕ) :=
    {v | (v ⟨2,h₂⟩,fun p : ↥S ↦ v ⟨p.val,hSat p⟩) ∈ fourMarkerExponentSet ↥S}
  let R (Q : Finset ℕ) : Set (↥Q → ℕ) := if h : Q = P then h.symm ▸ F else Set.univ
  have hR : R P = F := by simp [R]
  have h := integerBoundedPrimeBlockSet_finiteExceptionPrimeRule hd {P} R greedyExponents
    (fun Q hQ ↦ (mem_singleton.mp hQ).symm ▸ ⟨2,h₂⟩)
    (by
      intro Q hQ p hp
      have hp' : p ∈ P := (mem_singleton.mp hQ) ▸ hp
      rcases mem_insert.mp hp' with he | hs
      · exact he.symm ▸ Nat.prime_two
      · exact hPr p hs)
    (by
      intro Q hQ Q' hQ' hne
      exact (hne ((mem_singleton.mp hQ).trans (mem_singleton.mp hQ').symm)).elim)
    (by
      intro Q hQ
      rw [mem_singleton.mp hQ]
      exact hCard)
  convert h using 1
  ext n
  rw [finiteExceptionPrimeRule,Set.mem_setOf_eq,finitePrimeBlockRule,Set.mem_setOf_eq,singleton_biUnion,
    fourMarkerExchangeSet,Set.mem_setOf_eq]
  have hL : (∀ Q ∈ ({P} : Finset (Finset ℕ)),
        (fun p : ↥Q ↦ n.factorization p.val) ∈ R Q) ↔
      (n.factorization 2,fun p : ↥S ↦ n.factorization p.val) ∈ fourMarkerExponentSet ↥S := by
    constructor
    · intro h
      specialize h P (mem_singleton_self P)
      rw [hR] at h
      exact h
    · intro h Q hQ
      rw [mem_singleton.mp hQ,hR]
      exact h
  constructor
  · rintro ⟨hn,hF,hout⟩
    exact ⟨⟨hn,hL.mpr hF⟩,fun p hp hpP ↦ hout p hp
      (fun he ↦ hpP (he.symm ▸ h₂)) (fun hs ↦ hpP (hSat ⟨p,hs⟩))⟩
  · rintro ⟨⟨hn,hF⟩,hout⟩
    refine ⟨hn,hL.mp hF,fun p hp hp₂ hpS ↦ hout p hp ?_⟩
    change p ∉ insert 2 S
    exact fun hm ↦ (mem_insert.mp hm).elim hp₂ hpS

/-- All primes involved in the 1427 construction fit in a width-225 block. -/
theorem integerBoundedPrimeBlockSet_fourMarkerExchange1427 :
    IntegerBoundedPrimeBlockSet 225 (fourMarkerExchangeSet explicitOddPrimes) := by
  apply integerBoundedPrimeBlockSet_fourMarkerExchange _ (by decide)
  · exact fun p hp ↦ Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)
  · have h₂ : 2 ∈ explicitPrimes := Nat.mem_primesLE.mpr ⟨by decide,Nat.prime_two⟩
    rw [explicitOddPrimes,insert_erase h₂,explicitPrimes_card]

/-- The bounded three-term extremum at width 225 exceeds the Rankin density
by more than the article's explicit amount. -/
theorem one_div_ten_pow_lt_width225_sub_rankin :
    1 / (10 : ℝ)^596 <
      integerBoundedPrimeBlockDensitySupremum 3 225 - integerUpperDensity rankinSet := by
  obtain ⟨hFree,dR,dE,hR,hE,hgap⟩ := fourMarkerExchange1427_strictNaturalDensityGain
  have hmem :
      dE ∈ {a | ∃ A, IntegerBoundedPrimeBlockSet 225 A ∧ KTermGPFree 3 A ∧ a = integerUpperDensity A} :=
    ⟨fourMarkerExchangeSet explicitOddPrimes,integerBoundedPrimeBlockSet_fourMarkerExchange1427,
      kTermGPFree_three_of_threeGPFree hFree,(integerUpperDensity_eq_of_hasNaturalDensity hE).symm⟩
  have hBdd : BddAbove {a | ∃ A, IntegerBoundedPrimeBlockSet 225 A ∧ KTermGPFree 3 A ∧
      a = integerUpperDensity A} := ⟨1,by rintro a ⟨A,_,_,rfl⟩; exact integerUpperDensity_le_one A⟩
  rw [integerUpperDensity_eq_of_hasNaturalDensity hR]
  exact hgap.trans_le (sub_le_sub_right (le_csSup hBdd hmem) _)

end GRHArticle.ProgressionFree
