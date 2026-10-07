/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Module.ZLattice.Covolume
import OAI.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
import OAI.Combinatorics.Progressions.Linear.ShortGeneratingBasisBound

namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthonormalChart (b : OrthonormalBasis I ℝ E) : (I → ℝ) ≃L[ℝ] E :=
  (EuclideanSpace.equiv I ℝ).symm.trans b.repr.toContinuousLinearEquiv.symm

omit [FiniteDimensional ℝ E] in
theorem orthonormalChart_norm_le (b : OrthonormalBasis I ℝ E) (x : I → ℝ) :
    ‖orthonormalChart b x‖ ≤ (Fintype.card I : ℝ) * ‖x‖ := by
  change ‖b.repr.symm ((EuclideanSpace.equiv I ℝ).symm x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ∑ i, |x i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : I, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = _ := by simp

omit [FiniteDimensional ℝ E] in
theorem orthonormalChart_symm_norm_le (b : OrthonormalBasis I ℝ E) (x : E) :
    ‖(orthonormalChart b).symm x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  have h := PiLp.norm_apply_le (b.repr x) i
  simpa [orthonormalChart] using h

noncomputable def orthonormalCoordinateLattice (Λ : Submodule ℤ E)
    (b : OrthonormalBasis I ℝ E) : Submodule ℤ (I → ℝ) :=
  ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap

instance orthonormalCoordinateLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (b : OrthonormalBasis I ℝ E) : DiscreteTopology (orthonormalCoordinateLattice Λ b) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap))

instance orthonormalCoordinateLattice_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : OrthonormalBasis I ℝ E) :
    IsZLattice ℝ (orthonormalCoordinateLattice Λ b) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap))

variable [MeasurableSpace E] [BorelSpace E]

theorem orthonormalChart_measurePreserving (b : OrthonormalBasis I ℝ E) :
    MeasurePreserving (orthonormalChart b) :=
  b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp I)

theorem orthonormalCoordinateLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : OrthonormalBasis I ℝ E) :
    ZLattice.covolume (orthonormalCoordinateLattice Λ b) = ZLattice.covolume Λ :=
  ZLattice.covolume_comap Λ volume volume (orthonormalChart_measurePreserving b)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_short_euclidean_lattice_basis {E A : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (o : OrthonormalBasis (Fin n) ℝ E) (v : A → E) {R : ℝ}
    (hspan : span ℝ (Set.range v) = ⊤) (hmem : ∀ a, v a ∈ Λ)
    (hnorm : ∀ a, ‖v a‖ ≤ R) :
    ∃ b : Basis (Fin n) ℝ E,
      span ℤ (Set.range b) = Λ ∧
      (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n * ZLattice.covolume Λ ∧
      ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n * R := by
  classical
  let e := orthonormalChart o
  let L := orthonormalCoordinateLattice Λ o
  let B := IsZLattice.basis L
  let b₀ := B.ofZLatticeBasis ℝ L
  let u := fun a => e.symm (v a)
  have huSpan : span ℝ (Set.range u) = ⊤ := by
    change span ℝ (Set.range (e.symm.toLinearMap ∘ v)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hspan, Submodule.map_top]
    exact e.symm.toLinearEquiv.range
  have huMem : ∀ a, u a ∈ span ℤ (Set.range b₀) := by
    intro a
    rw [show span ℤ (Set.range b₀) = L from B.ofZLatticeBasis_span ℝ L]
    change e (e.symm (v a)) ∈ Λ
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hmem a
  have huNorm : ∀ a, ‖u a‖ ≤ R := fun a =>
    (orthonormalChart_symm_norm_le o (v a)).trans (hnorm a)
  obtain ⟨c, hcSpan, hcProd, hcNorm⟩ := exists_short_same_lattice_basis b₀ u huSpan huMem huNorm
  let b := c.map e.toLinearEquiv
  have hb (i) : b i = e (c i) := by simp [b]
  have hmap : L.map (e.toLinearMap.restrictScalars ℤ) = Λ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e (e.symm y) ∈ Λ
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  have hbSpan : span ℤ (Set.range b) = Λ := by
    calc
      _ = (span ℤ (Set.range c)).map (e.toLinearMap.restrictScalars ℤ) := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 2
      _ = L.map (e.toLinearMap.restrictScalars ℤ) := by
        rw [hcSpan, show span ℤ (Set.range b₀) = L from B.ofZLatticeBasis_span ℝ L]
      _ = Λ := hmap
  have hdet : |(Matrix.of c).det| = ZLattice.covolume Λ := by
    calc
      _ = |(Matrix.of b₀).det| := abs_det_eq_of_same_integer_span c b₀ hcSpan
      _ = ZLattice.covolume L := by
        have hb₀ : (b₀ : Fin n → Fin n → ℝ) = fun i => (B i : Fin n → ℝ) :=
          funext (fun i => Basis.ofZLatticeBasis_apply ℝ L B i)
        rw [hb₀]
        exact (ZLattice.covolume_eq_det L B).symm
      _ = ZLattice.covolume Λ := orthonormalCoordinateLattice_covolume Λ o
    rfl
  have hbNorm (i) : ‖b i‖ ≤ (n : ℝ) * ‖c i‖ := by
    rw [hb]
    simpa only [Fintype.card_fin] using orthonormalChart_norm_le o (c i)
  refine ⟨b, hbSpan, ?_, ?_⟩
  · calc
      _ ≤ ∏ i, (n : ℝ) * ‖c i‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hbNorm i)
      _ = (n : ℝ) ^ n * ∏ i, ‖c i‖ := by simp [Finset.prod_mul_distrib]
      _ ≤ (n : ℝ) ^ n * (minkowskiSecondConstant n * ZLattice.covolume Λ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
        simpa only [hdet] using hcProd
      _ = _ := by ring
  · intro i
    calc
      _ ≤ (n : ℝ) * ‖c i‖ := hbNorm i
      _ ≤ (n : ℝ) * ((n.factorial : ℝ) * minkowskiSecondConstant n * R) :=
        mul_le_mul_of_nonneg_left (hcNorm i) (Nat.cast_nonneg _)
      _ = _ := by ring

end Erdos3

end

end OAI
