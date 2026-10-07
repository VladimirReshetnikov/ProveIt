import OAI.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
import OAI.Combinatorics.Progressions.Lattices.IntegerCokernelExponent

namespace OAI

section

namespace Erdos3

theorem integerCokernel_character {I : Type*} (L : Submodule ℤ (I → ℤ))
    [Finite ((I → ℤ) ⧸ L.toAddSubgroup)] :
    ∃ χ : AddChar (I → ℤ) ℂ, orderOf χ = integerCokernelExponent L ∧
      ∀ x ∈ L, χ x = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_character_order_eq_exponent ((I → ℤ) ⧸ L.toAddSubgroup)
  let q := QuotientAddGroup.mk' L.toAddSubgroup
  refine ⟨characterPullback q ψ,
    (characterPullback_order q (QuotientAddGroup.mk'_surjective _) ψ).trans hψ, ?_⟩
  intro x hx
  change ψ (q x) = 1
  have hzero : q x = 0 := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hx
  rw [hzero, ψ.map_zero_eq_one]

theorem integerLattice_pivot_period {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hAin : A.mulVecLin.range ≤ L) :
    integerScalarLattice I (A.det.natAbs : ℤ) ≤ L := by
  rintro y ⟨z, rfl⟩
  change (A.det.natAbs : ℤ) • z ∈ L
  exact hAin (integerMatrixImage_natAbs_smul A z)

theorem integerCokernelExponent_le_det {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (hAin : A.mulVecLin.range ≤ L) :
    0 < integerCokernelExponent L ∧ integerCokernelExponent L ≤ A.det.natAbs := by
  let : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hA⟩
  have hp := integerLattice_pivot_period L A hAin
  let : Finite ((I → ℤ) ⧸ L.toAddSubgroup) := integerCokernel_finite L A.det.natAbs hp
  exact ⟨integerCokernelExponent_pos L,
    Nat.le_of_dvd (Int.natAbs_pos.mpr hA) (integerCokernelExponent_dvd_period L A.det.natAbs hp)⟩

theorem exists_bounded_annihilating_character {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (hAin : A.mulVecLin.range ≤ L) (B : ℕ) (hB : B < integerCokernelExponent L) :
    ∃ χ : AddChar (I → ℤ) ℂ,
      B < orderOf χ ∧ orderOf χ ≤ A.det.natAbs ∧ ∀ x ∈ L, χ x = 1 := by
  let : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hA⟩
  let : Finite ((I → ℤ) ⧸ L.toAddSubgroup) :=
    integerCokernel_finite L A.det.natAbs (integerLattice_pivot_period L A hAin)
  obtain ⟨χ, hχ, hann⟩ := integerCokernel_character L
  refine ⟨χ, ?_, ?_, hann⟩
  · rwa [hχ]
  · rw [hχ]
    exact (integerCokernelExponent_le_det L A hA hAin).2

end Erdos3

end

end OAI
