import GRHArticle.ProgressionFree.PolynomialNaturalExchange
import GRHArticle.ProgressionFree.PolynomialFiniteValuationDensity
import GRHArticle.ProgressionFree.PolynomialNaturalExchangeLocalMass

/-!
# Signed counting identity for the natural-density exchange

In each monic degree layer, the exchange removes the whole positive greedy
orthant and adds the cube on 1 and 2 except for its all-ones vector.
-/

namespace GRHArticle.ProgressionFree

open Polynomial
open scoped Classical BigOperators

variable {F : Type*} [Field F]

/-- The monic product rule with a greedy exterior and the same choice of local
exponents at each selected prime. -/
noncomputable def greedyExteriorProfile (S : Finset F[X]) (D : Set ℕ) : Set F[X] :=
  monicValuationRuleSet (replacePrimeRules S (fun _ ↦ greedyExponents) (fun _ ↦ D))

theorem mem_greedyExteriorProfile {S : Finset F[X]} {D : Set ℕ} {f : F[X]} :
    f ∈ greedyExteriorProfile S D ↔ f.Monic ∧
      (∀ p ∉ S, polynomialPrimeExponent p f ∈ greedyExponents) ∧
      ∀ p ∈ S, polynomialPrimeExponent p f ∈ D := by
  constructor
  · rintro ⟨hm,h⟩
    exact ⟨hm, fun p hp ↦ by simpa [replacePrimeRules,hp] using h p,
      fun p hp ↦ by simpa [replacePrimeRules,hp] using h p⟩
  · rintro ⟨hm,ho,hs⟩
    refine ⟨hm, fun p ↦ ?_⟩
    by_cases h : p ∈ S
    · simpa [replacePrimeRules, h] using hs p h
    · simpa [replacePrimeRules, h] using ho p h

/-- Pointwise counting identity for an exponent vector. -/
private theorem exchange_local_count {ι : Type*} (u : ι → ℕ) :
    (if u ∈ naturalExchangeRule greedyExponents ι then 1 else 0 : ℕ) +
    (if ∀ i, u i ∈ strictlyPositiveGreedyExponents then 1 else 0) +
    (if ∀ i, u i ∈ ({1}:Set ℕ) then 1 else 0) =
    (if ∀ i, u i ∈ greedyExponents then 1 else 0) +
    (if ∀ i, u i ∈ ({1,2}:Set ℕ) then 1 else 0) := by
  classical
  by_cases hz : ∃ i, u i = 0
  · obtain ⟨i,hi⟩ := hz
    have hn : ¬ ∀ j, u j ∈ strictlyPositiveGreedyExponents := fun h ↦ (h i).2 hi
    have hc : ¬ ∀ j, u j = 1 ∨ u j = 2 := by
      intro h; rcases h i with h | h <;> omega
    have h₁ : ¬ ∀ j, u j = 1 := by intro h; have := h i; omega
    simp [naturalExchangeRule, show ∃ j, u j = 0 from ⟨i,hi⟩, hn, hc, h₁]
  · have hpos (i : ι) : u i ≠ 0 := fun h ↦ hz ⟨i,h⟩
    have hOld : (∀ i, u i ∈ strictlyPositiveGreedyExponents) ↔ ∀ i, u i ∈ greedyExponents :=
      ⟨fun h i ↦ (h i).1, fun h i ↦ ⟨h i, hpos i⟩⟩
    by_cases hc : ∀ i, u i = 1 ∨ u i = 2
    · by_cases h₁ : ∀ i, u i = 1
      · simp [naturalExchangeRule, h₁, strictlyPositiveGreedyExponents, one_mem_greedyExponents]
      · have h₂ : ∃ i, u i = 2 := by
          push Not at h₁
          obtain ⟨i,hi⟩ := h₁
          exact ⟨i,(hc i).resolve_left hi⟩
        simp [naturalExchangeRule, hz, hOld, hc, h₁, h₂, Nat.add_comm]
    · have h₁ : ¬ ∀ i, u i = 1 := fun h ↦ hc (fun i ↦ Or.inl (h i))
      simp [naturalExchangeRule, hz, hOld, hc, h₁]

/-- The exchange in the polynomial convention, with nonzero leading scalars. -/
def polynomialNaturalExchangeFamily (S : Finset F[X]) : Set F[X] :=
  polynomialValuationFamily S greedyExponents (naturalExchangeRule greedyExponents ↥S)

variable [Fintype F]

/-- The signed count is exact at every degree before taking a limit. -/
theorem card_monicFamilyLayer_naturalExchange (S : Finset F[X]) (n : ℕ) :
    (monicFamilyLayer (polynomialNaturalExchangeFamily S) n).card +
    (monicFamilyLayer (greedyExteriorProfile S strictlyPositiveGreedyExponents) n).card +
    (monicFamilyLayer (greedyExteriorProfile S {1}) n).card =
    (monicFamilyLayer (greedyExteriorProfile S greedyExponents) n).card +
    (monicFamilyLayer (greedyExteriorProfile S {1,2}) n).card := by
  simp only [monicFamilyLayer, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  obtain ⟨hm,_⟩ := mem_monicLayer.mp hf
  let u (i : ↥S) := polynomialPrimeExponent i.val f
  have hsub (D : Set ℕ) : (∀ p ∈ S, polynomialPrimeExponent p f ∈ D) ↔ ∀ i, u i ∈ D :=
    ⟨fun h i ↦ h _ i.property, fun h p hp ↦ h ⟨p,hp⟩⟩
  by_cases ho : ∀ p ∉ S, polynomialPrimeExponent p f ∈ greedyExponents
  · have hprof (D : Set ℕ) : f ∈ greedyExteriorProfile S D ↔ ∀ i, u i ∈ D :=
      ⟨fun h ↦ (hsub D).mp (mem_greedyExteriorProfile.mp h).2.2,
        fun h ↦ mem_greedyExteriorProfile.mpr ⟨hm,ho,(hsub D).mpr h⟩⟩
    have hex : f ∈ polynomialNaturalExchangeFamily S ↔ u ∈ naturalExchangeRule greedyExponents ↥S :=
      ⟨fun h ↦ h.2.2, fun h ↦ ⟨hm.ne_zero,ho,h⟩⟩
    simp only [hex, hprof]
    have h := exchange_local_count u
    split_ifs at h ⊢ <;> omega
  · simp [mem_greedyExteriorProfile, polynomialNaturalExchangeFamily, polynomialValuationFamily, ho]

end GRHArticle.ProgressionFree
