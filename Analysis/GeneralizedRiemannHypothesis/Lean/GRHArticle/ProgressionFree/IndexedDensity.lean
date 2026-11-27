import GRHArticle.ProgressionFree.Density
import Mathlib.Logic.Equiv.Set

/-!
# Finite valuation patterns with indexed coordinates

A finite indexing type can enumerate distinct primes. This permits a split
between the primes changed by an exchange and the other primes being counted.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

/-- Finite valuation patterns on injectively indexed primes. -/
theorem hasNaturalDensity_indexedValuationPatterns {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (P : Finset (ι → ℕ)) :
    HasNaturalDensity {n | n ≠ 0 ∧ (fun i => n.factorization (p i)) ∈ P}
      (∑ e ∈ P, ∏ i, (1 - 1 / (p i : ℝ)) * (1 / (p i : ℝ)) ^ e i) := by
  classical
  let S := Finset.univ.image p
  have hS : ∀ q ∈ S, Nat.Prime q := by
    intro q hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    exact hi ▸ hprime i
  have hS_range : Set.range p = (S : Set ℕ) := by
    ext q
    simp [S]
  let e : ι ≃ ↥S := (Equiv.ofInjective p hinj).trans (Equiv.setCongr hS_range)
  have he (i : ι) : (e i).val = p i := rfl
  let a : (ι → ℕ) ≃ (↥S → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  let T := P.map a.toEmbedding
  have htuple (n : ℕ) : (fun q : ↥S => n.factorization q.val) =
      a (fun i => n.factorization (p i)) := by
    funext q
    change n.factorization q.val = n.factorization (p (e.symm q))
    rw [← he (e.symm q), e.apply_symm_apply]
  have hset : valuationPatterns S T = {n | n ≠ 0 ∧ (fun i => n.factorization (p i)) ∈ P} := by
    ext n
    simp only [valuationPatterns, Set.mem_setOf_eq, htuple, T, Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  have hsum :
      (∑ f ∈ T, ∏ q : ↥S, (1 - 1 / (q.val : ℝ)) * (1 / (q.val : ℝ)) ^ f q) =
        ∑ f ∈ P, ∏ i, (1 - 1 / (p i : ℝ)) * (1 / (p i : ℝ)) ^ f i := by
    unfold T
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro f _
    rw [← Equiv.prod_comp e]
    exact Fintype.prod_congr _ _ fun i => by
      change (1 - 1 / ((e i).val : ℝ)) * (1 / ((e i).val : ℝ)) ^ f (e.symm (e i)) = _
      rw [he, e.symm_apply_apply]
  simpa only [hset, hsum] using hasNaturalDensity_valuationPatterns S T hS

end GRHArticle.ProgressionFree
