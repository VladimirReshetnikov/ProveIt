import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_complexMean_sum_elim
    {A B R : Type*} [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    (f : ((A ⊕ B) → R) → ℂ) :
    (uniform (A → R)).complexMean (fun a =>
      (uniform (B → R)).complexMean (fun b => f (Sum.elim a b))) =
      (uniform ((A ⊕ B) → R)).complexMean f := by
  simp only [uniform_complexMean]
  calc
    _ = 𝔼 p : (A → R) × (B → R), f (Sum.elim p.1 p.2) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (A → R))
          (Finset.univ : Finset (B → R)) (fun a b => f (Sum.elim a b))).symm
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi (fun _ : A ⊕ B => R)).symm
      intro p
      rfl

theorem uniform_complexMean_sum_elim_retained
    {A B R Ω : Type*} [Fintype A] [Fintype B] [Fintype R] [Nonempty R] [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (f : Ω → ((A ⊕ B) → R) → ℂ) :
    (uniform (A → R)).complexMean (fun a => p.complexMean (fun ω =>
      (uniform (B → R)).complexMean (fun b => f ω (Sum.elim a b)))) =
      p.complexMean (fun ω => (uniform ((A ⊕ B) → R)).complexMean (f ω)) := by
  calc
    _ = p.complexMean (fun ω => (uniform (A → R)).complexMean (fun a =>
        (uniform (B → R)).complexMean (fun b => f ω (Sum.elim a b)))) := by
      simp only [uniform_complexMean]
      exact (p.complexMean_average (fun a ω => 𝔼 b : B → R, f ω (Sum.elim a b))).symm
    _ = _ := by
      congr 1
      funext ω
      exact uniform_complexMean_sum_elim (f ω)

theorem uniform_complexMean_sum_elim_flip
    {A B R : Type*} [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    (f : ((A ⊕ B) → R) → ℂ) :
    (uniform (B → R)).complexMean (fun b =>
      (uniform (A → R)).complexMean (fun a => f (Sum.elim a b))) =
      (uniform ((A ⊕ B) → R)).complexMean f := by
  calc
    _ = (uniform (A → R)).complexMean (fun a =>
        (uniform (B → R)).complexMean (fun b => f (Sum.elim a b))) := by
      simp only [uniform_complexMean]
      exact Finset.expect_comm _ _ _
    _ = _ := uniform_complexMean_sum_elim f

theorem uniform_complexMean_sum_elim_retained_flip
    {A B R Ω : Type*} [Fintype A] [Fintype B] [Fintype R] [Nonempty R] [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (f : Ω → ((A ⊕ B) → R) → ℂ) :
    (uniform (B → R)).complexMean (fun b =>
      (uniform (A → R)).complexMean (fun a => p.complexMean (fun ω =>
        f ω (Sum.elim a b)))) =
      p.complexMean (fun ω => (uniform ((A ⊕ B) → R)).complexMean (f ω)) := by
  calc
    _ = p.complexMean (fun ω => (uniform (B → R)).complexMean (fun b =>
        (uniform (A → R)).complexMean (fun a => f ω (Sum.elim a b)))) := by
      simp only [uniform_complexMean]
      simp_rw [← p.complexMean_average]
    _ = _ := by
      congr 1
      funext ω
      exact uniform_complexMean_sum_elim_flip (f ω)

end Erdos3.FiniteProbabilityWeights

end

end OAI
