import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformDependentSubtype_expect
    {P : Type*} [Fintype P] [DecidableEq P]
    (active : P → Prop) [DecidablePred active]
    (A : P → Type*) [∀ p, Fintype (A p)] (f : (∀ p, A p) → ℂ) :
    (𝔼 u : ∀ p, A p, f u) =
      𝔼 a : ∀ i : {p // active p}, A i.val,
        𝔼 s : ∀ i : {p // ¬active p}, A i.val,
          f ((Equiv.piEquivPiSubtypeProd active A).symm (a, s)) := by
  calc
    _ = 𝔼 pair : (∀ i : {p // active p}, A i.val) ×
        (∀ i : {p // ¬active p}, A i.val),
        f ((Equiv.piEquivPiSubtypeProd active A).symm pair) := by
      apply Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd active A)
      intro u
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product'
          (Finset.univ : Finset (∀ i : {p // active p}, A i.val))
          (Finset.univ : Finset (∀ i : {p // ¬active p}, A i.val))
          (fun a s => f ((Equiv.piEquivPiSubtypeProd active A).symm (a, s)))

theorem uniformDependentFinSubtype_expect
    {P : Type*} [Fintype P] [DecidableEq P]
    (active : P → Prop) [DecidablePred active]
    (L : P → ℕ) (f : (∀ p, Fin (L p)) → ℂ) :
    (𝔼 u : ∀ p, Fin (L p), f u) =
      𝔼 a : ∀ i : {p // active p}, Fin (L i.val),
        𝔼 s : ∀ i : {p // ¬active p}, Fin (L i.val),
          f ((Equiv.piEquivPiSubtypeProd active (fun p => Fin (L p))).symm (a, s)) :=
  uniformDependentSubtype_expect active (fun p => Fin (L p)) f

namespace FiniteProbabilityWeights

theorem uniform_complexMean_dependent_subtype
    {P : Type*} [Fintype P] [DecidableEq P]
    (active : P → Prop) [DecidablePred active]
    (A : P → Type*) [∀ p, Fintype (A p)] [∀ p, Nonempty (A p)]
    (f : (∀ p, A p) → ℂ) :
    (uniform (∀ p, A p)).complexMean f =
      (uniform (∀ i : {p // active p}, A i.val)).complexMean (fun a =>
        (uniform (∀ i : {p // ¬active p}, A i.val)).complexMean (fun s =>
          f ((Equiv.piEquivPiSubtypeProd active A).symm (a, s)))) := by
  simp only [uniform_complexMean]
  exact uniformDependentSubtype_expect active A f

end FiniteProbabilityWeights
end Erdos3

end

end OAI
