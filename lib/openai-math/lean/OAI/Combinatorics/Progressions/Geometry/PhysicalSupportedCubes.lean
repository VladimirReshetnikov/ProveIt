import OAI.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalCubeParametersEquiv (X : Type*) (dim : ℕ) :
    (X → (Unit ⊕ Fin dim) → ℤ) ≃ (Fin dim → X → ℤ) × (X → ℤ) where
  toFun v := (fun i x => v x (.inr i), fun x => v x (.inl ()))
  invFun p := fun x => Sum.elim (fun _ => p.2 x) (fun i => p.1 i x)
  left_inv v := by
    funext x i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  right_inv p := rfl

theorem physicalCubeParametersEquiv_vertex {X : Type*} (dim : ℕ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (ω : Fin dim → Bool) :
    physicalCubeVertexValue v (Finset.univ.filter (fun i => ω i)) =
      (physicalCubeParametersEquiv X dim v).2 +
        cubeShift (physicalCubeParametersEquiv X dim v).1 ω := by
  funext x
  change v x (.inl ()) + ∑ i ∈ Finset.univ.filter (fun i => ω i), v x (.inr i) =
    v x (.inl ()) + (∑ i, if ω i then (fun x => v x (.inr i)) else 0) x
  simp only [Finset.sum_filter, Finset.sum_apply]
  apply congrArg (fun z : ℤ => v x (.inl ()) + z)
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem physicalCubeParametersEquiv_support_iff {X : Type*} (dim : ℕ)
    (Q : Set (X → ℤ)) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    (∀ s : Finset (Fin dim), physicalCubeVertexValue v s ∈ Q) ↔
      ∀ ω : Fin dim → Bool, (physicalCubeParametersEquiv X dim v).2 +
        cubeShift (physicalCubeParametersEquiv X dim v).1 ω ∈ Q := by
  classical
  constructor
  · intro hv ω
    rw [← physicalCubeParametersEquiv_vertex]
    exact hv _
  · intro hv s
    have h := hv (fun i => decide (i ∈ s))
    rw [← physicalCubeParametersEquiv_vertex] at h
    simpa using h

def physicalSupportedCubeEquiv (X : Type*) (dim : ℕ) (Q : Set (X → ℤ)) :
    {v : X → (Unit ⊕ Fin dim) → ℤ // ∀ s, physicalCubeVertexValue v s ∈ Q} ≃
      SupportedCube dim Q where
  toFun v := ⟨physicalCubeParametersEquiv X dim v.val,
    (physicalCubeParametersEquiv_support_iff dim Q v.val).mp v.property⟩
  invFun p := ⟨(physicalCubeParametersEquiv X dim).symm p.val,
    (physicalCubeParametersEquiv_support_iff dim Q _).mpr (by
      simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv v := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv p := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

noncomputable def physicalIntegerBoxCubes {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) : Finset (X → (Unit ⊕ Fin dim) → ℤ) :=
  Finset.univ.image (fun p : SupportedCube dim (integerBox N : Set (X → ℤ)) =>
    (physicalCubeParametersEquiv X dim).symm p.val)

theorem mem_physicalIntegerBoxCubes {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    v ∈ physicalIntegerBoxCubes N dim ↔ ∀ s, physicalCubeVertexValue v s ∈ integerBox N := by
  classical
  constructor
  · intro hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact ((physicalSupportedCubeEquiv X dim (integerBox N : Set (X → ℤ))).symm p).property
  · intro hv
    let p := physicalSupportedCubeEquiv X dim (integerBox N : Set (X → ℤ)) ⟨v, hv⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, Equiv.symm_apply_apply _ _⟩

theorem physicalIntegerBoxCubes_card {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) :
    (physicalIntegerBoxCubes N dim).card = integerBoxCubeCount N dim := by
  classical
  rw [physicalIntegerBoxCubes, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, integerBoxCubeCount, Nat.card_eq_fintype_card]
  · exact (physicalCubeParametersEquiv X dim).symm.injective.comp Subtype.val_injective

theorem physicalIntegerBoxCubes_sum {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (∑ v ∈ physicalIntegerBoxCubes N dim, φ v) =
      ∑ p : SupportedCube dim (integerBox N : Set (X → ℤ)),
        φ ((physicalCubeParametersEquiv X dim).symm p.val) := by
  classical
  rw [physicalIntegerBoxCubes, Finset.sum_image]
  intro p _ t _ h
  exact Subtype.ext ((physicalCubeParametersEquiv X dim).symm.injective h)

theorem physicalIntegerBoxCubes_sum_eq_count_mul_mean {X : Type*}
    [Fintype X] [DecidableEq X] (N : X → ℕ) (dim : ℕ)
    (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (∑ v ∈ physicalIntegerBoxCubes N dim, φ v) =
      (integerBoxCubeCount N dim : ℂ) *
        𝔼 p : SupportedCube dim (integerBox N : Set (X → ℤ)),
          φ ((physicalCubeParametersEquiv X dim).symm p.val) := by
  rw [physicalIntegerBoxCubes_sum, integerBoxCubeCount, Nat.card_eq_fintype_card,
    ← nsmul_eq_mul, Fintype.card_smul_expect]

end Erdos3.BooleanCubeKernel

end

end OAI
