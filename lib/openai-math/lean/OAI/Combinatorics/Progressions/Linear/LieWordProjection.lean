import OAI.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion

namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable def lieWordSubalgebra : LieSubalgebra ℚ (WordPolynomial X) :=
  LieSubalgebra.lieSpan ℚ (WordPolynomial X)
    (Set.range (fun x : X => MonoidAlgebra.single (FreeSemigroup.of x) (1 : ℚ)))

theorem commutatorTree_mem_lieWordSubalgebra (t : FreeMagma X) :
    commutatorTree t ∈ lieWordSubalgebra := by
  induction t using FreeMagma.rec with
  | of x => exact LieSubalgebra.subset_lieSpan ⟨x, rfl⟩
  | mul u v hu hv => exact lieWordSubalgebra.lie_mem hu hv

theorem freeLieWordExpansion_range :
    (freeLieWordExpansion (X := X)).range = lieWordSubalgebra := by
  apply le_antisymm
  · intro p hp
    obtain ⟨x, rfl⟩ := (LieHom.mem_range _ _).mp hp
    apply freeLie_linear_induction (fun x => freeLieWordExpansion x ∈ lieWordSubalgebra)
    · simpa only [map_zero] using lieWordSubalgebra.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact lieWordSubalgebra.add_mem hx hy
    · intro r x hx
      rw [map_smul]
      exact lieWordSubalgebra.smul_mem r hx
    · intro t
      rw [freeLieWordExpansion_tree]
      exact commutatorTree_mem_lieWordSubalgebra t
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro p ⟨x, rfl⟩
    exact (LieHom.mem_range _ _).mpr ⟨FreeLieAlgebra.of ℚ x, freeLieWordExpansion_of x⟩

noncomputable def lieWordProjection : WordPolynomial X →ₗ[ℚ] WordPolynomial X :=
  freeLieWordExpansion.toLinearMap.comp (dynkinProjection (FreeLieAlgebra.of ℚ))

@[simp] theorem lieWordProjection_apply (p : WordPolynomial X) :
    lieWordProjection p = freeLieWordExpansion (dynkinProjection (FreeLieAlgebra.of ℚ) p) := rfl

theorem lieWordProjection_idempotent (p : WordPolynomial X) :
    lieWordProjection (lieWordProjection p) = lieWordProjection p := by
  simp only [lieWordProjection_apply, dynkinProjection_freeLieWordExpansion]

theorem lieWordProjection_eq_self_iff (p : WordPolynomial X) :
    lieWordProjection p = p ↔ p ∈ lieWordSubalgebra := by
  rw [← freeLieWordExpansion_range]
  constructor
  · intro h
    exact (LieHom.mem_range _ _).mpr ⟨dynkinProjection (FreeLieAlgebra.of ℚ) p, h⟩
  · intro h
    obtain ⟨x, rfl⟩ := (LieHom.mem_range _ _).mp h
    simp only [lieWordProjection_apply, dynkinProjection_freeLieWordExpansion]

end Erdos3

end

end OAI
