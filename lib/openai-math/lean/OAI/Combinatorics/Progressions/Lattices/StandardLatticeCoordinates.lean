/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.GramMatrix
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Estimates.IntegralOrthogonalSection
import OAI.Combinatorics.Progressions.Estimates.JointRationalSpaceGenerators
import OAI.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
import OAI.Combinatorics.Progressions.Lattices.EuclideanShortLatticeBasis

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {J : Type*} [Fintype J]

noncomputable def projectedIntegerLattice (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    Submodule ℤ Wᗮ := orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ

noncomputable def projectedIntegerGenerator (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) : Wᗮ :=
  Wᗮ.orthogonalProjectionOnto (EuclideanSpace.basisFun J ℝ i)

theorem projectedIntegerGenerator_mem (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) :
    projectedIntegerGenerator W i ∈ projectedIntegerLattice W := by
  refine ⟨EuclideanSpace.basisFun J ℝ i, ?_, rfl⟩
  exact subset_span (Set.mem_range_self i)

theorem projectedIntegerGenerator_norm_le (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) :
    ‖projectedIntegerGenerator W i‖ ≤ 1 := by
  have h := Wᗮ.norm_orthogonalProjectionOnto_apply_le (EuclideanSpace.basisFun J ℝ i)
  simpa only [projectedIntegerGenerator, OrthonormalBasis.norm_eq_one] using h

theorem projectedIntegerGenerator_span (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    span ℝ (Set.range (projectedIntegerGenerator W)) = ⊤ := by
  change span ℝ (Set.range (Wᗮ.orthogonalProjectionOnto.toLinearMap ∘
    (EuclideanSpace.basisFun J ℝ).toBasis)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro w
  refine ⟨w.val, ?_⟩
  apply Subtype.ext
  exact Wᗮ.starProjection_eq_self_iff.mpr w.property

theorem projectedIntegerGenerator_integer_span (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    span ℤ (Set.range (projectedIntegerGenerator W)) = projectedIntegerLattice W := by
  rw [projectedIntegerLattice, orthogonalLatticeImage, standardEuclideanLattice,
    Submodule.map_span, ← Set.range_comp]
  rfl

theorem standardLatticeSection_full_of_integral_span (W : Submodule ℝ (EuclideanSpace ℝ J))
    (hspan : span ℝ {x : W | ∀ i, ∃ n : ℤ, x.val i = n} = ⊤) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W) := by
  constructor
  convert hspan using 1
  congr 1
  ext x
  change (x.val ∈ standardEuclideanLattice J) ↔ _
  rw [mem_standardEuclideanLattice]
  simp only [Set.mem_ofPred_eq, eq_comm]

instance projectedIntegerLattice_discrete (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    DiscreteTopology (projectedIntegerLattice W) := by
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice J) Wᗮ) :=
    latticeSection_orthogonal_full (standardEuclideanLattice J)
      (by rw [standardEuclideanLattice_self_dual]) W
  let : IsZLattice ℝ (latticeSection (euclideanDualLattice (standardEuclideanLattice J)) Wᗮ) := by
    constructor
    change span ℝ {x : Wᗮ | x.val ∈ euclideanDualLattice (standardEuclideanLattice J)} = ⊤
    rw [standardEuclideanLattice_self_dual]
    exact IsZLattice.span_top (K := ℝ) (L := latticeSection (standardEuclideanLattice J) Wᗮ)
  exact orthogonalLatticeImage_discrete (standardEuclideanLattice J) Wᗮ

instance projectedIntegerLattice_full (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    IsZLattice ℝ (projectedIntegerLattice W) := by
  let : DiscreteTopology (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_discrete W
  exact orthogonalLatticeImage_full (standardEuclideanLattice J) Wᗮ

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

theorem standardEuclideanLattice_covolume (J : Type*) [Fintype J] :
    ZLattice.covolume (standardEuclideanLattice J) = 1 := by
  classical
  let b := EuclideanSpace.basisFun J ℝ
  have hg : Matrix.gram ℝ b.toBasis = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr b.orthonormal
  have hs := zspan_covolume_sq_eq_det_gram_fintype b.toBasis
  rw [hg, Matrix.det_one] at hs
  have hp := ZLattice.covolume_pos (standardEuclideanLattice J) volume
  change ZLattice.covolume (standardEuclideanLattice J) ^ 2 = 1 at hs
  nlinarith

theorem projectedIntegerLattice_covolume {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) *
      ZLattice.covolume (projectedIntegerLattice W) = 1 := by
  have hW : Wᗮᗮ = W := W.orthogonal_orthogonal
  let : DiscreteTopology (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_discrete W
  let : IsZLattice ℝ (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_full W
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice J) Wᗮᗮ) :=
    (congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ J) =>
      IsZLattice ℝ (latticeSection (standardEuclideanLattice J) V)) hW).mpr inferInstance
  have h := orthogonalLattice_covolume (standardEuclideanLattice J) Wᗮ
  have hc := congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ J) =>
    ZLattice.covolume (latticeSection (standardEuclideanLattice J) V)) hW
  rw [hc, standardEuclideanLattice_covolume] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix NNReal

variable {J R I : Type*} [Fintype J] [Fintype R]

noncomputable def rationalKernelAxisBound (Q : Matrix R J ℚ) (H : ℕ) : ℝ :=
  (matrixDenominator Q : ℝ) * (((Fintype.card J : ℝ) + 1) * ((H : ℝ) + 1))

theorem projectedIntegerLattice_norm_inv_le_of_rational_kernel
    (Q : Matrix R J ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.ker (Matrix.mulVecLin (fun r j => (Q r j : ℝ))) = W)
    {H : ℕ} (hQ : ∀ r j, RationalHeightLE (Q r j) H)
    {z : (euclideanSubspace W)ᗮ}
    (hz : z ∈ projectedIntegerLattice (euclideanSubspace W)) (hne : z ≠ 0) :
    ‖z‖⁻¹ ≤ rationalKernelAxisBound Q H := by
  classical
  obtain ⟨x, hx, hxz⟩ := hz
  change (euclideanSubspace W)ᗮ.orthogonalProjectionOnto x = z at hxz
  let y : EuclideanSpace ℝ J := x - z.val
  have hy : y ∈ euclideanSubspace W := by
    have h := (euclideanSubspace W)ᗮ.sub_starProjection_mem_orthogonal x
    rw [Submodule.orthogonal_orthogonal] at h
    simpa only [Submodule.starProjection_apply, hxz] using h
  have hQy : (fun r j => (Q r j : ℝ)) *ᵥ WithLp.ofLp y = 0 := by
    change WithLp.ofLp y ∈ W at hy
    rw [← hW] at hy
    exact hy
  have hxgrid : WithLp.ofLp x ∈ realDenominatorGrid 1 := by
    choose a ha using (mem_standardEuclideanLattice J x).mp hx
    refine ⟨a, ?_⟩
    ext j
    simpa only [Pi.smul_apply, Nat.cast_one, one_smul] using ha j
  have hQx : (fun r j => (Q r j : ℝ)) *ᵥ WithLp.ofLp x ≠ 0 := by
    intro hzero
    have hxW : x ∈ euclideanSubspace W := by
      change WithLp.ofLp x ∈ W
      rw [← hW]
      exact hzero
    have hproj : (euclideanSubspace W)ᗮ.orthogonalProjectionOnto x = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        ((euclideanSubspace W).le_orthogonal_orthogonal hxW)
    exact hne (hxz.symm.trans hproj)
  have hsep : 1 ≤ rationalKernelAxisBound Q H *
      dist (WithLp.ofLp x) (WithLp.ofLp y) := by
    by_contra! hsmall
    apply hQx
    apply rational_matrix_kernel_separation Q (H : ℝ≥0)
      (fun r j => (hQ r j).abs_real_le) 1 (by decide)
      (WithLp.ofLp x) (WithLp.ofLp y) hxgrid hQy
    simpa only [Nat.mul_one, rationalKernelAxisBound, NNReal.coe_natCast] using hsmall
  have hdist : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ ‖z‖ := by
    rw [dist_eq_norm]
    have he : WithLp.ofLp x - WithLp.ofLp y = WithLp.ofLp z.val := by
      ext j
      change x j - (x j - z.val j) = z.val j
      ring
    rw [he]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
      (fun j => PiLp.norm_apply_le z.val j)
  have hbound : 1 ≤ rationalKernelAxisBound Q H * ‖z‖ :=
    hsep.trans (mul_le_mul_of_nonneg_left hdist (by
      unfold rationalKernelAxisBound
      positivity))
  exact (inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hne)).mpr hbound

theorem basisAxisScale_le_of_rational_kernel
    (Q : Matrix R J ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.ker (Matrix.mulVecLin (fun r j => (Q r j : ℝ))) = W)
    {H : ℕ} (hQ : ∀ r j, RationalHeightLE (Q r j) H)
    (b : Basis I ℝ (euclideanSubspace W)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace W))
    (i : I) :
    basisAxisScale b i ≤ ⌈rationalKernelAxisBound Q H⌉₊ := by
  apply Nat.ceil_mono
  apply projectedIntegerLattice_norm_inv_le_of_rational_kernel Q W hW hQ
  · rw [← hb]
    exact subset_span (Set.mem_range_self i)
  · exact b.ne_zero i

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem exists_bounded_integral_span_of_rational_range
    {J C : Type*} [Fintype J] [Fintype C]
    (B : Matrix J C ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin = W)
    {H : ℕ} (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ v : C → euclideanSubspace W,
      span ℝ (Set.range v) = ⊤ ∧
      (∀ j, v j ∈ latticeSection (standardEuclideanLattice J) (euclideanSubspace W)) ∧
      ∀ j, ‖v j‖ ≤ (Fintype.card J : ℝ) * H ^ (Fintype.card J * Fintype.card C) := by
  classical
  obtain ⟨D, hD, _, z, hz, hzH⟩ :=
    exists_bounded_integer_array (fun ij : J × C => B ij.1 ij.2) (fun ij => hB ij.1 ij.2)
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hzr (i : J) (j : C) : (z (i, j) : ℝ) = (D : ℝ) * (B i j : ℝ) := by
    exact_mod_cast hz (i, j)
  have hcol (j : C) : (fun i => (B i j : ℝ)) ∈ W := by
    rw [← hW, Matrix.range_mulVecLin]
    exact subset_span ⟨j, rfl⟩
  have hmem (j : C) : WithLp.toLp 2 (fun i => (z (i, j) : ℝ)) ∈ euclideanSubspace W := by
    change (fun i => (z (i, j) : ℝ)) ∈ W
    have he : (fun i => (z (i, j) : ℝ)) = (D : ℝ) • (fun i => (B i j : ℝ)) :=
      funext (fun i => hzr i j)
    rw [he]
    exact W.smul_mem (D : ℝ) (hcol j)
  let v : C → euclideanSubspace W := fun j => ⟨WithLp.toLp 2 (fun i => (z (i, j) : ℝ)), hmem j⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    have hx : WithLp.ofLp x.val ∈ W := x.property
    obtain ⟨y, hy⟩ := hW.ge hx
    have heq : x = ∑ j, (y j / D) • v j := by
      apply Subtype.ext
      ext i
      have hi := congrFun hy i
      change (∑ j, (B i j : ℝ) * y j) = x.val i at hi
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum,
        WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hi]
      apply Finset.sum_congr rfl
      intro j _
      rw [hzr]
      field_simp
    rw [heq]
    exact sum_mem (fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩))
  · intro j
    change (v j).val ∈ standardEuclideanLattice J
    exact (mem_standardEuclideanLattice J _).mpr (fun i => ⟨z (i, j), rfl⟩)
  · intro j
    calc
      ‖v j‖ ≤ ∑ i, |(z (i, j) : ℝ)| := euclidean_norm_le_sum_abs (v j).val
      _ ≤ ∑ _ : J, (H : ℝ) ^ (Fintype.card J * Fintype.card C) := by
        apply Finset.sum_le_sum
        intro i _
        have hb := hzH (i, j)
        rw [Fintype.card_prod] at hb
        have hr : |z (i, j)| ≤ (H ^ (Fintype.card J * Fintype.card C) : ℕ) := by
          simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hb)
        exact_mod_cast hr
      _ = _ := by simp

theorem rationalRangeLattice_full
    {J C : Type*} [Fintype J] [Fintype C]
    (B : Matrix J C ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin = W)
    {H : ℕ} (hB : ∀ i j, RationalHeightLE (B i j) H) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J) (euclideanSubspace W)) := by
  obtain ⟨v, hv, hmem, _⟩ := exists_bounded_integral_span_of_rational_range B W hW hB
  constructor
  apply top_unique
  rw [← hv]
  apply span_mono
  rintro _ ⟨j, rfl⟩
  exact hmem j

theorem jointRationalSpaceLattice_full
    {J C V : Type*} [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (hA : ∀ v j, RationalHeightLE (A v j) R) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J)
      (euclideanSubspace (VectorPolynomial.jointRationalSpace B A))) := by
  obtain ⟨P, hP, hW⟩ := VectorPolynomial.exists_jointRationalSpace_generators B A hH hR hB hA
  exact rationalRangeLattice_full P _ hW hP

end Erdos3

end

section

namespace Erdos3

open Module Submodule BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_short_projected_integer_basis {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n *
        ZLattice.covolume (projectedIntegerLattice W) ∧
      ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n := by
  simpa only [mul_one] using exists_short_euclidean_lattice_basis
    (projectedIntegerLattice W) (stdOrthonormalBasis ℝ Wᗮ) (projectedIntegerGenerator W)
    (projectedIntegerGenerator_span W) (projectedIntegerGenerator_mem W)
    (projectedIntegerGenerator_norm_le W)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

noncomputable def standardLatticeIntegerLift (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    (J → ℤ) →ₗ[ℤ] standardEuclideanLattice D :=
  latticeIntegerLift (standardEuclideanLattice D) W
    (integerBasisOfReal (projectedIntegerLattice W) bP hP)

theorem standardLatticeIntegerLift_projection (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (z : J → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W bP hP z).val =
      bP.equivFun.symm (fun j => (z j : ℝ)) := by
  have h := latticeIntegerLift_projection (standardEuclideanLattice D) W
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) z
  exact h.trans (integerBasisOfReal_synthesis (projectedIntegerLattice W) bP hP z)

noncomputable def standardLatticeCoordinates (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    (D → ℤ) ≃ₗ[ℤ] (J ⊕ I → ℤ) :=
  (standardEuclideanLinearEquiv D).trans
    ((latticeSignedCoordinates (standardEuclideanLattice D) W bW
      (integerBasisOfReal (projectedIntegerLattice W) bP hP)).trans
      (LinearEquiv.sumArrowLequivProdArrow J I ℤ ℤ).symm)

theorem standardLatticeCoordinates_reconstruction (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (β : D → ℤ) :
    (standardEuclideanPoint D β).val +
        (standardLatticeIntegerLift W bP hP
          (fun j => standardLatticeCoordinates W bW bP hP β (Sum.inl j))).val =
      (bW.equivFun.symm (fun i => standardLatticeCoordinates W bW bP hP β (Sum.inr i))).val.val := by
  rw [← standardEuclideanLinearEquiv_eq_point]
  exact latticeSignedCoordinates_reconstruction (standardEuclideanLattice D) W bW
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) (standardEuclideanLinearEquiv D β)

theorem standardLatticeCoordinates_projection (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (β : D → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardEuclideanPoint D β).val =
      -bP.equivFun.symm (fun j => (standardLatticeCoordinates W bW bP hP β (Sum.inl j) : ℝ)) := by
  have h := congrArg Wᗮ.orthogonalProjectionOnto
    (standardLatticeCoordinates_reconstruction W bW bP hP β)
  rw [map_add, standardLatticeIntegerLift_projection,
    W.orthogonalProjectionOnto_orthogonal_apply_eq_zero
      (bW.equivFun.symm (fun i => standardLatticeCoordinates W bW bP hP β (Sum.inr i))).val.property] at h
  exact eq_neg_of_add_eq_zero_left h

theorem standardLatticeCoordinates_residue [DecidableEq D]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (M : ℕ) [NeZero M] :
    ∃ A : Matrix (J ⊕ I) D ℤ,
      (∀ i j, 0 ≤ A i j ∧ A i j < M) ∧
      ∀ β, integerResidueMap (J ⊕ I) M (standardLatticeCoordinates W bW bP hP β) =
        integerResidueMatrix A M *ᵥ integerResidueMap D M β :=
  exists_bounded_integerMap_residue_matrix (standardLatticeCoordinates W bW bP hP).toLinearMap M

end Erdos3

end

end OAI
