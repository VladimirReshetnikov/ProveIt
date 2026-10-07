import Mathlib.Algebra.Module.ZLattice.Basic
import OAI.Combinatorics.Progressions.Estimates.OrthogonalSection
import OAI.Combinatorics.Progressions.Estimates.ScaledSectionGram
import OAI.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
import OAI.Combinatorics.Progressions.Lattices.LatticeSheetHaar

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem rational_vector_mem_span_integer_points {κ : Type*} [Fintype κ]
    (U : Submodule ℝ (κ → ℝ)) (q : κ → ℚ) (hq : (fun i => (q i : ℝ)) ∈ U) :
    (fun i => (q i : ℝ)) ∈ Submodule.span ℝ
      {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U} := by
  classical
  let D := arrayDenominator q
  let z := clearedArray q
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (arrayDenominator_pos q).ne'
  have he : (fun i => (z i : ℝ)) = (D : ℝ) • (fun i => (q i : ℝ)) := by
    funext i
    change (clearedArray q i : ℝ) = (arrayDenominator q : ℝ) * (q i : ℝ)
    exact_mod_cast clearedArray_cast q i
  have hz : (fun i => (z i : ℝ)) ∈ U := by rw [he]; exact U.smul_mem _ hq
  have hs : (fun i => (z i : ℝ)) ∈ Submodule.span ℝ
      {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U} := Submodule.subset_span ⟨⟨z, rfl⟩, hz⟩
  have hinv := (Submodule.span ℝ {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U}).smul_mem
    (D : ℝ)⁻¹ hs
  simpa only [he, smul_smul, inv_mul_cancel₀ hD, one_smul] using hinv

theorem exists_rational_matrix_height {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) : ∃ H : ℕ, 1 ≤ H ∧ ∀ i j, RationalHeightLE (A i j) H := by
  classical
  let H := max 1 (Finset.univ.sup fun ij : ι × κ => max (A ij.1 ij.2).num.natAbs (A ij.1 ij.2).den)
  refine ⟨H, le_max_left _ _, ?_⟩
  intro i j
  have hmax : max (A i j).num.natAbs (A i j).den ≤ H :=
    (Finset.le_sup (f := fun ij : ι × κ => max (A ij.1 ij.2).num.natAbs (A ij.1 ij.2).den)
      (Finset.mem_univ (i, j))).trans (le_max_right _ _)
  exact ⟨(le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax⟩

theorem real_rational_kernel_eq_span_integer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) :
    LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ))) =
      Submodule.span ℝ {x : κ → ℝ | x ∈ realIntegerGrid ∧
        x ∈ LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ)))} := by
  classical
  obtain ⟨H, hH, hA⟩ := exists_rational_matrix_height A
  obtain ⟨S, hS, _⟩ := exists_bounded_rational_image_section A hH hA
  let Ar : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
  let Sr : Matrix κ ι ℝ := fun i j => (S i j : ℝ)
  let P : Matrix κ κ ℚ := 1 - S * A
  let Pr : Matrix κ κ ℝ := fun i j => (P i j : ℝ)
  have hSr : Ar * Sr * Ar = Ar := real_matrix_image_section A S hS
  have hPr : Pr = (1 : Matrix κ κ ℝ) - Sr * Ar := by
    ext i j
    change (P i j : ℝ) = (if i = j then 1 else 0) - ∑ k, (S i k : ℝ) * (A k j : ℝ)
    by_cases hij : i = j <;> simp [P, Matrix.sub_apply, Matrix.mul_apply, hij]
  have hzero : Ar * (1 - Sr * Ar) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSr, sub_self]
  have hrange : LinearMap.range ((1 - Sr * Ar).mulVecLin) = LinearMap.ker Ar.mulVecLin := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change Ar *ᵥ ((1 - Sr * Ar) *ᵥ y) = 0
      rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
    · intro hx
      change Ar *ᵥ x = 0 at hx
      refine ⟨x, ?_⟩
      change (1 - Sr * Ar) *ᵥ x = x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        hx, Matrix.mulVec_zero, sub_zero]
  have hspan : Submodule.span ℝ (Set.range Pr.col) = LinearMap.ker Ar.mulVecLin := by
    rw [← Matrix.range_mulVecLin, hPr]
    exact hrange
  apply le_antisymm
  · change LinearMap.ker Ar.mulVecLin ≤ _
    calc
      LinearMap.ker Ar.mulVecLin = Submodule.span ℝ (Set.range Pr.col) := hspan.symm
      _ ≤ _ := by
        apply Submodule.span_le.mpr
        rintro x ⟨j, rfl⟩
        apply rational_vector_mem_span_integer_points _ (P.col j)
        exact hspan ▸ (Submodule.subset_span ⟨j, rfl⟩)
  · exact Submodule.span_le.mpr (fun _ hx => hx.2)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem kernel_eq_span_integer_inter_of_basis
    {E ι κ : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (b : Basis κ ℝ E) (Λ : Submodule ℤ E) (hb : Submodule.span ℤ (Set.range b) = Λ)
    (π : E →ₗ[ℝ] (ι → ℝ)) (hπ : ∀ j, π (b j) ∈ realIntegerGrid) :
    LinearMap.ker π = Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
  classical
  choose z hz using hπ
  let A : Matrix ι κ ℚ := fun i j => (z j i : ℚ)
  let Ar : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
  let f : (κ → ℝ) →ₗ[ℝ] E := b.equivFun.symm.toLinearMap
  have hA (y : κ → ℝ) : π (b.equivFun.symm y) = Ar *ᵥ y := by
    funext i
    rw [b.equivFun_symm_apply, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (z j i : ℝ) = π (b j) i := congrFun (hz j) i
    rw [← hj]
    simp only [Ar, A, Rat.cast_intCast, mul_comm]
  have hmap : (LinearMap.ker Ar.mulVecLin).map f ≤
      Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
    change (LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ)))).map f ≤ _
    rw [real_rational_kernel_eq_span_integer, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, ⟨⟨a, ha⟩, hy⟩, rfl⟩
    apply Submodule.subset_span
    constructor
    · rw [← hb, b.mem_span_iff_repr_mem ℤ]
      intro j
      refine ⟨a j, ?_⟩
      change (a j : ℝ) = b.equivFun (b.equivFun.symm y) j
      rw [LinearEquiv.apply_symm_apply]
      exact congrFun ha j
    · change π (b.equivFun.symm y) = 0
      rw [hA]
      exact hy
  apply le_antisymm
  · intro x hx
    apply hmap
    refine ⟨b.equivFun x, ?_, b.equivFun.symm_apply_apply x⟩
    change Ar *ᵥ b.equivFun x = 0
    rw [← hA, LinearEquiv.symm_apply_apply]
    exact hx
  · apply Submodule.span_le.mpr
    intro x hx
    exact hx.2

end Erdos3

end

section

namespace Erdos3

open Module

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

noncomputable def latticeKernel : Submodule ℤ (LinearMap.ker π) :=
  ZLattice.comap ℝ Λ (LinearMap.ker π).subtype

instance latticeKernel_discrete [DiscreteTopology Λ] : DiscreteTopology (latticeKernel Λ π) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

theorem kernel_eq_span_lattice_inter [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    LinearMap.ker π = Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
  let b := (Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  exact kernel_eq_span_integer_inter_of_basis b Λ
    ((Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ)
    π (fun j => hπ _ (by
      simpa only [b, Basis.ofZLatticeBasis_apply] using ((Free.chooseBasis ℤ Λ) j).property))

theorem latticeKernel_full [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) : IsZLattice ℝ (latticeKernel Λ π) := by
  constructor
  apply (Submodule.map_injective_of_injective (LinearMap.ker π).injective_subtype)
  rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
  refine Eq.trans ?_ (kernel_eq_span_lattice_inter Λ π hπ).symm
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨⟨x, hzero⟩, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

def latticeImageProjection : Λ →ₗ[ℤ] latticeImage Λ π :=
  ((π.restrictScalars ℤ).comp Λ.subtype).codRestrict (latticeImage Λ π)
    (fun x => ⟨x.val, x.property, rfl⟩)

theorem latticeImageProjection_apply (x : Λ) :
    (latticeImageProjection Λ π x).val = π x.val := rfl

theorem latticeImageProjection_surjective : Function.Surjective (latticeImageProjection Λ π) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def latticeKernelEquiv :
    latticeKernel Λ π ≃ₗ[ℤ] LinearMap.ker (latticeImageProjection Λ π) where
  toFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
  invFun x := ⟨⟨x.val.val, congrArg Subtype.val
    (show latticeImageProjection Λ π x.val = 0 from x.property)⟩, x.val.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl
  map_smul' _a _x := rfl

theorem latticeKernelEquiv_apply (x : latticeKernel Λ π) :
    ((latticeKernelEquiv Λ π x).val : E) = x.val.val := rfl

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_split_basis
    {E ι α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))
    (bK : Basis α ℤ (latticeKernel Λ π)) (bI : Basis β ℤ (latticeImage Λ π)) :
    ∃ b : Basis (α ⊕ β) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, π (b (Sum.inr j) : E) = (bI j).val) := by
  let : Free ℤ (latticeImage Λ π) := Free.of_basis bI
  obtain ⟨b, hbK, hbI⟩ := exists_basis_of_surjection (latticeImageProjection Λ π)
    (latticeImageProjection_surjective Λ π) (bK.map (latticeKernelEquiv Λ π)) bI
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hbK]
    rfl
  · intro j
    exact congrArg Subtype.val (hbI j)

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_basis_covolume_factor
    {E ι α β : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [Fintype β] [DecidableEq β]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ)) [IsZLattice ℝ (latticeKernel Λ π)]
    (bK : Basis α ℤ (latticeKernel Λ π)) (bI : Basis β ℤ (latticeImage Λ π)) :
    ∃ b : Basis (α ⊕ β) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, π (b (Sum.inr j) : E) = (bI j).val) ∧
      ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeKernel Λ π) ^ 2 *
        (Matrix.gram ℝ (fun j : β => (b (Sum.inr j) : E) -
          (LinearMap.ker π).starProjection (b (Sum.inr j) : E))).det := by
  classical
  obtain ⟨b, hbK, hbI⟩ := exists_lattice_split_basis Λ π bK bI
  refine ⟨b, hbK, hbI, ?_⟩
  let bR := b.ofZLatticeBasis ℝ Λ
  let bKR := bK.ofZLatticeBasis ℝ (latticeKernel Λ π)
  have hval (i : α) : bR (Sum.inl i) = (bKR i : E) := by
    simpa only [bR, bKR, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : Submodule.span ℝ (Set.range (fun i : α => bR (Sum.inl i))) =
      LinearMap.ker π := by
    rw [show (fun i : α => bR (Sum.inl i)) = (fun i : α => (bKR i : E)) from funext hval]
    change Submodule.span ℝ (Set.range ((LinearMap.ker π).subtype ∘ bKR)) = _
    rw [Set.range_comp, ← Submodule.map_span, bKR.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hkernelGram : (Matrix.gram ℝ (fun i : α => bR (Sum.inl i))).det =
      ZLattice.covolume (latticeKernel Λ π) ^ 2 := by
    have he : Matrix.gram ℝ (fun i : α => bR (Sum.inl i)) = Matrix.gram ℝ bKR := by
      ext i j
      simp only [Matrix.gram_apply, hval]
      rfl
    rw [he]
    exact (lattice_covolume_sq_eq_gram (latticeKernel Λ π) bK).symm
  have hblock := gram_det_orthogonal_block bR
  dsimp only at hblock
  rw [hspan, hkernelGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  simpa only [bR, Basis.ofZLatticeBasis_apply] using hblock

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_index_covolume_factor
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    ∃ L : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (L y) = y) ∧
      (∀ x, L (π x) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ ^ 2 =
        ZLattice.covolume (latticeKernel Λ π) ^ 2 *
        ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) ^ 2 *
        (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det := by
  classical
  let H := latticeImage Λ π
  let K := latticeKernel Λ π
  let : DiscreteTopology H := latticeImage_discrete Λ π hinteger
  let : IsZLattice ℝ H := latticeImage_full Λ π hsurj
  let : IsZLattice ℝ K := latticeKernel_full Λ π hinteger
  let bK := Free.chooseBasis ℤ K
  let bI := IsZLattice.basis H
  let B := bI.ofZLatticeBasis ℝ H
  obtain ⟨L, hright, hsection⟩ := exists_orthogonal_section π hsurj
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg π hxy
    simpa only [hright] using h
  obtain ⟨b, _, hbI, hcov⟩ := exists_lattice_basis_covolume_factor Λ π bK bI
  have hw (j : ι) : (b (Sum.inr j) : E) -
      (LinearMap.ker π).starProjection (b (Sum.inr j) : E) = L (B j) := by
    rw [← hsection]
    apply congrArg L
    simpa only [B, Basis.ofZLatticeBasis_apply] using hbI j
  have hcov' : ZLattice.covolume Λ ^ 2 = ZLattice.covolume K ^ 2 *
      (Matrix.gram ℝ (fun j : ι => L (B j))).det := by
    simpa only [hw] using hcov
  have hgram := gram_det_injective_map_basis L hL (Pi.basisFun ℝ ι) B
  have hB : (B : ι → (ι → ℝ)) = fun j => (bI j).val := by
    funext j
    exact bI.ofZLatticeBasis_apply ℝ H j
  have hdet : |(Pi.basisFun ℝ ι).det B| =
      ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) := by
    rw [Pi.basisFun_det_apply, hB]
    exact (ZLattice.covolume_eq_det H bI).symm.trans
      (integer_lattice_covolume_eq_index H (latticeImage_le_integer Λ π hinteger))
  have hsq := congrArg (fun t : ℝ => t ^ 2) hdet
  rw [sq_abs] at hsq
  refine ⟨L, hright, hsection, ?_⟩
  rw [hgram, hsq] at hcov'
  simpa only [mul_assoc] using hcov'

end Erdos3

end

section

namespace Erdos3

theorem exists_lattice_covolume_identity
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    ∃ L : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (L y) = y) ∧
      (∀ x, L (π x) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π) *
        ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) *
        Real.sqrt (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det := by
  let : IsZLattice ℝ (latticeKernel Λ π) := latticeKernel_full Λ π hinteger
  obtain ⟨L, hright, hsection, hsq⟩ := exists_lattice_index_covolume_factor Λ π hinteger hsurj
  refine ⟨L, hright, hsection, ?_⟩
  have h := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (ZLattice.covolume_pos (latticeKernel Λ π) MeasureTheory.volume).le,
    Real.sqrt_sq (Nat.cast_nonneg _)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem exists_scaled_lattice_covolume_identity
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) :
    ∃ G : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (G y) = fun i => T i * y i) ∧
      (∀ x, G (fun i => π x i / T i) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π) *
        (((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) /
          ∏ i, T i) *
        Real.sqrt (Matrix.gram ℝ (fun i : ι => G (Pi.basisFun ℝ ι i))).det := by
  obtain ⟨L, hright, hsection, hcov⟩ := exists_lattice_covolume_identity Λ π hinteger hsurj
  let D := coordinateScaleEquiv T (fun i => (hT i).ne')
  let G := L.comp D.toLinearMap
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg π hxy
    simpa only [hright] using h
  have hscale := scaled_section_gram_sqrt L hL T hT
  have hprod : 0 < ∏ i, T i := Finset.prod_pos (fun i _ => hT i)
  have hroot : Real.sqrt (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det =
      Real.sqrt (Matrix.gram ℝ (fun i : ι => G (Pi.basisFun ℝ ι i))).det / ∏ i, T i := by
    apply (eq_div_iff hprod.ne').mpr
    dsimp only [G, D, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hscale]
    ring
  refine ⟨G, ?_, ?_, ?_⟩
  · intro y
    exact hright (D y)
  · intro x
    change L (D (D.symm (π x))) = x - (LinearMap.ker π).starProjection x
    rw [LinearEquiv.apply_symm_apply]
    exact hsection x
  · rw [hroot] at hcov
    rw [hcov]
    ring

end Erdos3

end

end OAI
