import Mathlib.Data.Set.Finite.Basic

/-! A forward-invariant predicate for an injection on a finite type is also
backward invariant.  Unlike iteration induction, this recovers predecessors.
-/
namespace DiophantineConsistency.ProofSimplification.FiniteInvariant

theorem reflect {A : Type*} [Finite A] (f : A → A)
    (hf : Function.Injective f) (P : A → Prop)
    (hP : ∀ i, P i → P (f i)) (i : A) (hi : P (f i)) : P i := by
  have hb := ((Set.toFinite {i | P i}).injOn_iff_bijOn_of_mapsTo hP).mp hf.injOn
  obtain ⟨j, hj, hji⟩ := hb.surjOn hi
  exact hf hji ▸ hj

#print axioms reflect
end DiophantineConsistency.ProofSimplification.FiniteInvariant
