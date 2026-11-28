import GRHArticle.ProgressionFree.Rankin

/-!
# A joint exchange of prime exponents

Keep the old exponent vectors with a zero coordinate. Replace the strictly
positive vectors by the cube on 1 and 2 with its all-ones vector removed.
The result forbids nonconstant progressions with nonnegative coordinate steps.
-/

namespace GRHArticle.ProgressionFree

/-- The joint exponent rule at the selected primes. The index type can be infinite. -/
def naturalExchangeRule (A : Set ℕ) (ι : Type*) : Set (ι → ℕ) :=
  {u | ((∀ i, u i ∈ A) ∧ ∃ i, u i = 0) ∨
       ((∀ i, u i = 1 ∨ u i = 2) ∧ ∃ i, u i = 2)}

/-- A zero coordinate forces an accepted vector to belong to the original rule. -/
theorem mem_old_of_naturalExchangeRule_zero {A : Set ℕ} {ι : Type*} {u : ι → ℕ}
    (hu : u ∈ naturalExchangeRule A ι) {i : ι} (hi : u i = 0) : ∀ j, u j ∈ A := by
  rcases hu with h | h
  · exact h.1
  · rcases h.1 i with h | h <;> omega

/-- Nonnegative coordinate steps in an accepted three-term progression must all
vanish. Any progression-free starting set omitting 2 satisfies the theorem. -/
theorem naturalExchangeRule_step_eq_zero {A : Set ℕ} (hA : ThreeAPFree A) (h₂ : 2 ∉ A)
    {ι : Type*} {u h : ι → ℕ} (hu : u ∈ naturalExchangeRule A ι)
    (hv : (fun i ↦ u i + h i) ∈ naturalExchangeRule A ι)
    (hw : (fun i ↦ u i + 2 * h i) ∈ naturalExchangeRule A ι) :
    ∀ i, h i = 0 := by
  rcases hw with ⟨hw, k, hk⟩ | ⟨hw, _⟩
  · change u k + 2 * h k = 0 at hk
    have hu' := mem_old_of_naturalExchangeRule_zero hu (i := k) (by omega)
    have hv' := mem_old_of_naturalExchangeRule_zero hv (i := k)
      (show u k + h k = 0 by omega)
    intro i
    have he := hA (hu' i) (hv' i) (hw i) (show u i + (u i + 2 * h i) =
      (u i + h i) + (u i + h i) by omega)
    change u i = u i + h i at he
    omega
  · intro k
    by_contra hk
    have hb (i : ι) : u i + 2 * h i = 1 ∨ u i + 2 * h i = 2 := hw i
    have hk' := hb k
    have hu' := mem_old_of_naturalExchangeRule_zero hu (i := k) (by omega)
    have hone (i : ι) : u i + h i = 1 := by
      have hi := hb i
      have hne : u i ≠ 2 := fun he ↦ h₂ (he ▸ hu' i)
      omega
    rcases hv with ⟨_, i, hi⟩ | ⟨_, i, hi⟩ <;> specialize hone i <;>
      change u i + h i = _ at hi <;> omega

theorem two_notMem_greedyExponents : 2 ∉ greedyExponents := by
  intro h
  have := ((mem_greedyExponents_iff 2).mp h).1
  omega

/-- The article's ternary greedy exponent exchange in arbitrary dimension. -/
theorem greedy_naturalExchangeRule_step_eq_zero {ι : Type*} {u h : ι → ℕ}
    (hu : u ∈ naturalExchangeRule greedyExponents ι)
    (hv : (fun i ↦ u i + h i) ∈ naturalExchangeRule greedyExponents ι)
    (hw : (fun i ↦ u i + 2 * h i) ∈ naturalExchangeRule greedyExponents ι) :
    ∀ i, h i = 0 :=
  naturalExchangeRule_step_eq_zero threeAPFree_greedyExponents two_notMem_greedyExponents hu hv hw

end GRHArticle.ProgressionFree
