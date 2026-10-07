import OAI.Combinatorics.Progressions.Fourier.DivisibleCharacterExtension
import OAI.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts

namespace OAI

section

namespace Erdos3

open Module

variable {ι κ : Type} [Fintype ι] [Fintype κ] {N : ℕ} [NeZero N]
  (η : (ι → ℤ) →+ ZMod N) (b : Basis κ ℤ (cyclicIntegerKernel η))

noncomputable def cyclicKernelRealCoordinates : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ) :=
  (b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)).equivFun

noncomputable def cyclicKernelCoordinateCharacter (i : κ) :
    (ι → ℤ) →+ AddCircle (1 : ℝ) where
  toFun x := (cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ)
  map_zero' := by simp
  map_add' x y := by simp only [map_add, Pi.add_apply, AddCircle.coe_add]

theorem cyclicKernelCoordinateCharacter_eq_zero (x : ι → ℤ) (hx : η x = 0) (i : κ) :
    cyclicKernelCoordinateCharacter η b i x = 0 := by
  let y : cyclicIntegerKernel η :=
    ⟨integerVectorRealMap x, (integerVectorRealMap_mem_cyclicIntegerKernel η x).mpr hx⟩
  change ((b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)).repr (y : ι → ℝ) i :
    AddCircle (1 : ℝ)) = 0
  rw [Basis.ofZLatticeBasis_repr_apply]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨b.repr y i, by simp⟩

theorem cyclicKernelCoordinateCharacters_eq_zero_iff (x : ι → ℤ) :
    (∀ i, cyclicKernelCoordinateCharacter η b i x = 0) ↔ η x = 0 := by
  refine ⟨?_, fun hx i => cyclicKernelCoordinateCharacter_eq_zero η b x hx i⟩
  intro h
  apply (integerVectorRealMap_mem_cyclicIntegerKernel η x).mp
  rw [← b.ofZLatticeBasis_span ℝ (cyclicIntegerKernel η)]
  rw [Basis.mem_span_iff_repr_mem]
  intro i
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (h i)
  exact ⟨z, by simpa [cyclicKernelRealCoordinates, Basis.equivFun_apply] using hz⟩

theorem cyclicKernelCoordinateCharacters_eq_iff (x y : ι → ℤ) :
    (∀ i, cyclicKernelCoordinateCharacter η b i x =
      cyclicKernelCoordinateCharacter η b i y) ↔ η x = η y := by
  rw [← sub_eq_zero, ← map_sub, ← cyclicKernelCoordinateCharacters_eq_zero_iff η b]
  simp only [map_sub, sub_eq_zero]

theorem exists_cyclic_kernel_real_frequencies :
    ∃ t : κ → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
      ∀ (x : ι → ℤ) (n : ℤ), η x = (n : ZMod N) → ∀ i,
        ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
          AddCircle (1 : ℝ)) = (((n : ℝ) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  have h := fun i => exists_cyclic_real_character_lift η
    (cyclicKernelCoordinateCharacter η b i)
    (fun x hx => cyclicKernelCoordinateCharacter_eq_zero η b x hx i)
  choose t ht hperiod hformula using h
  exact ⟨t, ht, hperiod, fun x n hn i => hformula i x n hn⟩

theorem cyclicKernelCoordinateCharacters_injOn
    (S : Set (ι → ℤ)) (hη : Set.InjOn η S) :
    Set.InjOn (fun x i => cyclicKernelCoordinateCharacter η b i x) S := by
  intro x hx y hy hxy
  apply hη hx hy
  exact (cyclicKernelCoordinateCharacters_eq_iff η b x y).mp (congrFun hxy)

theorem exists_affine_cyclic_kernel_real_frequencies
    (h₀ : ZMod N) :
    ∃ t : κ → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
      ∀ (h : ZMod N) (x : ι → ℤ), h = h₀ + η x → ∀ i,
        ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
          AddCircle (1 : ℝ)) =
            ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨t, ht, hperiod, hformula⟩ := exists_cyclic_kernel_real_frequencies η b
  refine ⟨t, ht, hperiod, ?_⟩
  intro h x hx i
  have he : η x = (((h.val : ℤ) - h₀.val : ℤ) : ZMod N) := by
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hx, add_sub_cancel_left]
  simpa only [Int.cast_sub, Int.cast_natCast] using hformula x _ he i

end Erdos3

end

end OAI
