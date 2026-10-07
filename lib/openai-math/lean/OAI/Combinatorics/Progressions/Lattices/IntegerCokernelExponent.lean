import Mathlib.GroupTheory.Exponent
import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod

namespace OAI

section

namespace Erdos3

noncomputable def integerCokernelExponent {I : Type*} (L : Submodule ℤ (I → ℤ)) : ℕ :=
  AddMonoid.exponent ((I → ℤ) ⧸ L.toAddSubgroup)

theorem integerCokernel_finite {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Finite ((I → ℤ) ⧸ L.toAddSubgroup) := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hindex : L.toAddSubgroup.index ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h
    exact (pow_ne_zero _ (NeZero.ne m)) h.symm
  let : L.toAddSubgroup.FiniteIndex := ⟨hindex⟩
  infer_instance

theorem integerCokernelExponent_pos {I : Type*} (L : Submodule ℤ (I → ℤ))
    [Finite ((I → ℤ) ⧸ L.toAddSubgroup)] : 0 < integerCokernelExponent L :=
  AddMonoid.ExponentExists.of_finite.exponent_pos

theorem integerCokernelExponent_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) :
    integerScalarLattice I (integerCokernelExponent L : ℤ) ≤ L := by
  rintro y ⟨z, rfl⟩
  change (integerCokernelExponent L : ℤ) • z ∈ L
  rw [natCast_zsmul]
  have h := AddMonoid.exponent_nsmul_eq_zero (QuotientAddGroup.mk' L.toAddSubgroup z)
  rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h
  exact h

theorem integerCokernelExponent_dvd_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    integerCokernelExponent L ∣ m := by
  apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.toAddSubgroup x
  rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  change m • z ∈ L
  have h := hperiod ((integerScalarLattice_mem (m : ℤ) _).mpr ⟨z, rfl⟩)
  simpa only [natCast_zsmul] using h

end Erdos3

end

end OAI
