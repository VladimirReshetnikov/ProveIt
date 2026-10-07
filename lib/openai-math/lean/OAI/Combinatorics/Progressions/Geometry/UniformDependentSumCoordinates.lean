import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformDependentSum_expect
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (A : G ⊕ P → Type*) [∀ k, Fintype (A k)] (f : (∀ k, A k) → ℂ) :
    (𝔼 u : ∀ k, A k, f u) =
      𝔼 g : ∀ i, A (Sum.inl i), 𝔼 p : ∀ j, A (Sum.inr j), f (Sum.rec g p) := by
  calc
    _ = 𝔼 gp : (∀ i, A (Sum.inl i)) × (∀ j, A (Sum.inr j)), f (Sum.rec gp.1 gp.2) := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi A)
      intro u
      congr 1
      funext k
      cases k <;> rfl
    _ = _ := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product' (Finset.univ : Finset (∀ i, A (Sum.inl i)))
          (Finset.univ : Finset (∀ j, A (Sum.inr j)))
          (fun g p => f (Sum.rec g p))

theorem uniformDependentFin_expect
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (L : G ⊕ P → ℕ) (f : (∀ k, Fin (L k)) → ℂ) :
    (𝔼 u : ∀ k, Fin (L k), f u) =
      𝔼 g : ∀ i, Fin (L (Sum.inl i)), 𝔼 p : ∀ j, Fin (L (Sum.inr j)), f (Sum.rec g p) :=
  uniformDependentSum_expect (fun k => Fin (L k)) f

namespace FiniteProbabilityWeights

theorem uniform_complexMean_dependent_sum
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (A : G ⊕ P → Type*) [∀ k, Fintype (A k)] [∀ k, Nonempty (A k)]
    (f : (∀ k, A k) → ℂ) :
    (uniform (∀ k, A k)).complexMean f =
      (uniform (∀ i, A (Sum.inl i))).complexMean (fun g =>
        (uniform (∀ j, A (Sum.inr j))).complexMean (fun p => f (Sum.rec g p))) := by
  simp only [uniform_complexMean]
  exact uniformDependentSum_expect A f

theorem uniform_complexMean_dependent_fin_sum
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (L : G ⊕ P → ℕ) [∀ k, NeZero (L k)] (f : (∀ k, Fin (L k)) → ℂ) :
    (uniform (∀ k, Fin (L k))).complexMean f =
      (uniform (∀ i, Fin (L (Sum.inl i)))).complexMean (fun g =>
        (uniform (∀ j, Fin (L (Sum.inr j)))).complexMean (fun p => f (Sum.rec g p))) :=
  uniform_complexMean_dependent_sum (fun k => Fin (L k)) f

end FiniteProbabilityWeights
end Erdos3

end

end OAI
