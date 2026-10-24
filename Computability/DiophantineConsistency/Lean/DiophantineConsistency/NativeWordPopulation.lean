import DiophantineConsistency.NativeCyclicConvolution
import DiophantineConsistency.MaskPopulation

/-! # Binary population of a radix word and an injective sparse stencil -/

namespace DiophantineConsistency.NativeWordPopulation

open NativeCyclicConvolution Jones1982
open scoped BigOperators

variable {n : ℕ} [NeZero n]

theorem word_population (v : ℕ) (a : ZMod n → ℕ) (ha : ∀ k, a k < 2^v) :
    σ 2 (word (2^v) a) = ∑ k, σ 2 (a k) := by
  rw [word_eq_ofDigits, MaskPopulation.population_ofDigits v _ (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ha _)]
  simp only [List.map_ofFn,Fin.sum_ofFn,Function.comp_apply]
  exact Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _ (fun _ => rfl)

/-- Binary population is additive on an injectively placed finite table.
The statement is independent of the concrete word length. -/
theorem sparse_population {m : ℕ} (v : ℕ) (p : Fin m → ZMod n)
    (hp : Function.Injective p) (a : Fin m → ℕ) (ha : ∀ i, a i < 2^v) :
    σ 2 (word (2^v) (fun k => ∑ i : Fin m, if p i = k then a i else 0)) =
      ∑ i, σ 2 (a i) := by
  classical
  have he (k : ZMod n) :
      (∑ i : Fin m, if p i = k then a i else 0) < 2^v ∧
      σ 2 (∑ i : Fin m, if p i = k then a i else 0) =
        ∑ i : Fin m, if p i = k then σ 2 (a i) else 0 := by
    by_cases hk : ∃ i, p i = k
    · obtain ⟨i,rfl⟩ := hk
      simp only [hp.eq_iff]
      simpa using ha i
    · have hh (i : Fin m) : p i ≠ k := fun h => hk ⟨i,h⟩
      simp only [if_neg (hh _),Finset.sum_const_zero,σ_two_zero]
      exact ⟨by positivity,trivial⟩
  rw [word_population v _ (fun k => (he k).1)]
  simp_rw [(he _).2]
  rw [Finset.sum_comm]
  simp

end DiophantineConsistency.NativeWordPopulation
