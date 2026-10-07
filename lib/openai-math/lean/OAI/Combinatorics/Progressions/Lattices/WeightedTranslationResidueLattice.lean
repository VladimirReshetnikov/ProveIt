import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationNilmanifold

namespace OAI

section

namespace Erdos3

variable {B : Type*}

noncomputable def integerTranslationResidueSubgroup (M : ℕ) :
    Subgroup (PolynomialTranslationGroupOver ℤ B) where
  carrier := {γ | ∀ i, (γ.base i : ZMod M) = 0}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro a b ha hb i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply, Int.cast_add,
      ha i, hb i, add_zero]
  inv_mem' := by
    intro a ha i
    simp only [PolynomialTranslationGroupOver.base_inv, Pi.neg_apply, Int.cast_neg,
      ha i, neg_zero]

@[simp] theorem mem_integerTranslationResidueSubgroup (M : ℕ)
    (γ : PolynomialTranslationGroupOver ℤ B) :
    γ ∈ integerTranslationResidueSubgroup M ↔ ∀ i, (γ.base i : ZMod M) = 0 := Iff.rfl

noncomputable def integerPolynomialTranslationResidueCover (M : ℕ) :
    Subgroup (PolynomialTranslationGroupOver ℝ B) :=
  (integerTranslationResidueSubgroup (B := B) M).map
    (PolynomialTranslationGroupOver.map (Int.castRingHom ℝ))

theorem integerPolynomialTranslationResidueCover_le (M : ℕ) :
    integerPolynomialTranslationResidueCover (B := B) M ≤ integerPolynomialTranslationSubgroup := by
  rintro g ⟨γ, _, rfl⟩
  exact ⟨γ, rfl⟩

theorem integerTranslationResidueSubgroup_of_multiple (M : ℕ)
    (z : B → ℤ) (Q : MvPolynomial B ℤ) :
    (⟨fun i => (M : ℤ) * z i, Q⟩ : PolynomialTranslationGroupOver ℤ B) ∈
      integerTranslationResidueSubgroup M := by
  intro i
  change (((M : ℤ) * z i : ℤ) : ZMod M) = 0
  simp

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

noncomputable def weightedTranslationResidueLattice (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    Subgroup (weightedFiltration w d hwd).Group :=
  ((integerTranslationResidueSubgroup (B := σ) M).map PolynomialTranslationGroup.fromInteger).comap
    (bchTranslationHom w d hw hwd)

theorem weightedTranslationResidueLattice_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    weightedTranslationResidueLattice w d hw hwd M ≤ weightedTranslationLattice w d hwd := by
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd]
  rintro g ⟨z, _, hz⟩
  exact ⟨z, hz⟩

omit [Fintype σ] in
private theorem integerTranslation_base_pow
    (γ : PolynomialTranslationGroupOver ℤ σ) (n : ℕ) (i : σ) :
    (γ ^ n).base i = (n : ℤ) * γ.base i := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, PolynomialTranslationGroupOver.base_mul, Pi.add_apply, ih,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul]

theorem weightedTranslationResidueLattice_contains_power_cover
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    subgroupPowerCover (weightedTranslationLattice w d hwd) M ≤
      weightedTranslationResidueLattice w d hw hwd M := by
  apply (subgroupPowerCover_le_iff _ _ M).mpr
  intro g hg
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd] at hg
  obtain ⟨γ, hγ⟩ := hg
  refine ⟨γ ^ M, ?_, ?_⟩
  · intro i
    rw [integerTranslation_base_pow]
    simp
  · rw [map_pow, map_pow, hγ]

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationResidueLattice_inner_grid (M : ℕ) :
    scaledIntegerGrid (d.factorial * M) ⊆
      bchSubgroupCoordinates (weightedOrderedBasis w d hw)
        (weightedTranslationResidueLattice w d hw hwd M) := by
  have hinner := subgroupPowerCover_inner_grid (weightedOrderedBasis w d hw)
    (weightedTranslationLattice w d hwd) d.factorial M (weightedOrderedBasis_inner_grid w d hw hwd)
  intro x hx
  apply weightedTranslationResidueLattice_contains_power_cover w d hw hwd M
  apply hinner
  simpa only [Nat.mul_comm] using hx

theorem weightedTranslationResidueLattice_outer_grid (M : ℕ) :
    bchSubgroupCoordinates (weightedOrderedBasis w d hw)
      (weightedTranslationResidueLattice w d hw hwd M) ⊆
        denominatorGrid (d.factorial * M) := by
  intro x hx
  have h0 := weightedOrderedBasis_outer_grid w d hw hwd
    (weightedTranslationResidueLattice_le w d hw hwd M hx)
  simpa only [Nat.mul_comm] using denominator_grid_subset_mul d.factorial M h0

end Erdos3.PolynomialTranslationLie

end

end OAI
