/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Estimates.GaussianScaledShortVectorBound
import OAI.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection
import OAI.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
import OAI.Combinatorics.Progressions.Geometry.SignedSplitCoordinates
import OAI.Combinatorics.Progressions.Linear.BasisSurjectionSection

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeBasisEquiv (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) : (I → ℤ) ≃ Λ :=
  (b.restrictScalars ℤ).equivFun.symm.toEquiv.trans
    (LinearEquiv.ofEq _ _ hb).toEquiv

theorem latticeBasisEquiv_coordinates (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) (i : I) :
    b.equivFun (latticeBasisEquiv Λ b hb z).val i = (z i : ℝ) := by
  change b.repr (((b.restrictScalars ℤ).equivFun.symm z) : E) i = _
  have h := b.restrictScalars_repr_apply ℤ ((b.restrictScalars ℤ).equivFun.symm z) i
  change (algebraMap ℤ ℝ)
    ((b.restrictScalars ℤ).equivFun ((b.restrictScalars ℤ).equivFun.symm z) i) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  simpa using h.symm

theorem latticeBasisEquiv_synthesis (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) :
    (latticeBasisEquiv Λ b hb z).val = b.equivFun.symm (fun i => (z i : ℝ)) := by
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  exact latticeBasisEquiv_coordinates Λ b hb z i

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_primitive_lattice_normal (Λ : Submodule ℤ E)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤) (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ)) :
    ∃ (m : ℤ) (ζ w : E), m ≠ 0 ∧ ξ = (m : ℝ) • ζ ∧ ζ ≠ 0 ∧ ‖ζ‖ ≤ ‖ξ‖ ∧
      (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ζ x = (n : ℝ)) ∧ w ∈ Λ ∧ inner ℝ ζ w = 1 := by
  have hf : normalFunctional ξ ≠ 0 := by
    intro hz
    have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f ξ) hz
    change inner ℝ ξ ξ = 0 at he
    rw [real_inner_self_eq_norm_sq] at he
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    nlinarith
  obtain ⟨m, g, w, hm, hfg, hgint, hwΛ, hwg, _⟩ :=
    exists_primitive_lattice_functional Λ (normalFunctional ξ) hspan hint hf
  let ζ := (m : ℝ)⁻¹ • ξ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hg (x : E) : inner ℝ ζ x = g x := by
    have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hfg
    change inner ℝ ξ x = (m : ℝ) * g x at he
    simp only [ζ, real_inner_smul_left, he]
    field_simp
  have hsplit : ξ = (m : ℝ) • ζ := by
    simp only [ζ, smul_smul, mul_inv_cancel₀ hmR, one_smul]
  refine ⟨m, ζ, w, hm, hsplit, smul_ne_zero (inv_ne_zero hmR) hξ, ?_, ?_, hwΛ, ?_⟩
  · have ha : (1 : ℝ) ≤ |(m : ℝ)| := by
      have hmpos : (0 : ℤ) < |m| := abs_pos.mpr hm
      have hma : (1 : ℤ) ≤ |m| := by omega
      exact_mod_cast hma
    have hnorm : ‖ζ‖ = ‖ξ‖ / |(m : ℝ)| := by
      simp only [ζ, norm_smul, Real.norm_eq_abs, abs_inv, div_eq_mul_inv, mul_comm]
    rw [hnorm]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one ha)).mpr
    exact le_mul_of_one_le_right (norm_nonneg _) ha
  · intro x hx
    rw [hg]
    exact hgint x hx
  · rw [hg]
    exact hwg

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanDualLattice (Λ : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ

theorem mem_euclideanDualLattice (Λ : Submodule ℤ E) (ξ : E) :
    ξ ∈ euclideanDualLattice Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ) := by
  simp only [euclideanDualLattice, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, innerₗ_apply_apply]
  exact forall_congr' (fun _ => forall_congr' (fun _ => exists_congr (fun _ => eq_comm)))

theorem realInner_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

variable [FiniteDimensional ℝ E]

theorem euclideanDualLattice_eq_span_dualBasis (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate
        ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ))) := by
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E) realInner_nondegenerate
    ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, Module.Basis.ofZLatticeBasis_span] using h

instance euclideanDualLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : DiscreteTopology (euclideanDualLattice Λ) := by
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  infer_instance

instance euclideanDualLattice_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : IsZLattice ℝ (euclideanDualLattice Λ) := by
  constructor
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  exact IsZLattice.span_top (K := ℝ)

theorem euclideanDualLattice_involutive (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : euclideanDualLattice (euclideanDualLattice Λ) = Λ := by
  have hsymm : LinearMap.BilinForm.IsSymm (innerₗ E) := ⟨fun _ _ => real_inner_comm _ _⟩
  have h := LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (R := ℤ) (innerₗ E)
    realInner_nondegenerate hsymm ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, Module.Basis.ofZLatticeBasis_span] using h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_bounded_primitive_lattice_normal (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0) (hξdual : ξ ∈ euclideanDualLattice Λ) :
    ∃ (m : ℤ) (ζ w : E), m ≠ 0 ∧ ξ = (m : ℝ) • ζ ∧ ζ ≠ 0 ∧ ‖ζ‖ ≤ ‖ξ‖ ∧
      ζ ∈ euclideanDualLattice Λ ∧ w ∈ Λ ∧ inner ℝ ζ w = 1 ∧
      |(m : ℝ)| ≤ Real.exp Real.pi * ‖ξ‖ * latticeGaussianMass (euclideanDualLattice Λ) 1 0 := by
  obtain ⟨m, ζ, w, hm, hsplit, hζ, hnorm, hint, hwΛ, hw⟩ :=
    exists_primitive_lattice_normal Λ (IsZLattice.span_top (K := ℝ)) ξ hξ
      ((mem_euclideanDualLattice Λ ξ).mp hξdual)
  have hζdual := (mem_euclideanDualLattice Λ ζ).mpr hint
  exact ⟨m, ζ, w, hm, hsplit, hζ, hnorm, hζdual, hwΛ, hw,
    latticeGaussianMass_controls_integer_factor (euclideanDualLattice Λ) ξ ζ hζdual hζ m hsplit⟩

end Erdos3

end

section

namespace Erdos3

open Submodule Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def latticeSection (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Submodule ℤ W := ZLattice.comap ℝ Λ W.subtype

instance latticeSection_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (W : Submodule ℝ E) : DiscreteTopology (latticeSection Λ W) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

noncomputable def orthogonalLatticeImage (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Submodule ℤ W := Λ.map (W.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)

theorem orthogonalLatticeImage_le_dual_section (Λ : Submodule ℤ E)
    (W : Submodule ℝ E) :
    orthogonalLatticeImage Λ W ≤ euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_euclideanDualLattice _ _).mpr
  intro y hy
  have hy' : (y : E) ∈ euclideanDualLattice Λ := hy
  obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ y.val).mp hy' x hx
  refine ⟨n, ?_⟩
  change inner ℝ (W.orthogonalProjectionOnto x) y = (n : ℝ)
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, real_inner_comm]
  exact hn

theorem orthogonalLatticeImage_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection (euclideanDualLattice Λ) W)] :
    DiscreteTopology (orthogonalLatticeImage Λ W) := by
  have hdis : DiscreteTopology (euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W)) :=
    euclideanDualLattice_discrete _
  have hd : IsDiscrete (euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W) : Set W) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr hdis
  exact isDiscrete_iff_discreteTopology.mp (hd.mono (orthogonalLatticeImage_le_dual_section Λ W))

theorem orthogonalLatticeImage_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E) [DiscreteTopology (orthogonalLatticeImage Λ W)] :
    IsZLattice ℝ (orthogonalLatticeImage Λ W) := by
  constructor
  change span ℝ (W.orthogonalProjectionOnto.toLinearMap '' (Λ : Set E)) = ⊤
  rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro w
  refine ⟨w.val, ?_⟩
  apply Subtype.ext
  exact W.starProjection_eq_self_iff.mpr w.property

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

noncomputable def standardEuclideanLattice : Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)

instance standardEuclideanLattice_discrete : DiscreteTopology (standardEuclideanLattice ι) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)))

instance standardEuclideanLattice_full : IsZLattice ℝ (standardEuclideanLattice ι) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)))

theorem mem_standardEuclideanLattice (x : EuclideanSpace ℝ ι) :
    x ∈ standardEuclideanLattice ι ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
  change x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) ↔ _
  rw [(EuclideanSpace.basisFun ι ℝ).toBasis.mem_span_iff_repr_mem ℤ x]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

noncomputable def standardEuclideanPoint (z : ι → ℤ) : standardEuclideanLattice ι :=
  ⟨WithLp.toLp 2 (fun i => (z i : ℝ)), (mem_standardEuclideanLattice ι _).mpr (fun i => ⟨z i, rfl⟩)⟩

@[simp]
theorem standardEuclideanPoint_apply (z : ι → ℤ) (i : ι) :
    (standardEuclideanPoint ι z : EuclideanSpace ℝ ι) i = (z i : ℝ) := rfl

theorem standardEuclideanPoint_bijective : Function.Bijective (standardEuclideanPoint ι) := by
  constructor
  · intro z w h
    funext i
    have hi := congrArg (fun x : standardEuclideanLattice ι => (x : EuclideanSpace ℝ ι) i) h
    exact Int.cast_injective (α := ℝ) hi
  · intro x
    choose z hz using (mem_standardEuclideanLattice ι (x : EuclideanSpace ℝ ι)).mp x.property
    refine ⟨z, ?_⟩
    apply Subtype.ext
    ext i
    exact hz i

noncomputable def standardEuclideanEquiv : (ι → ℤ) ≃ standardEuclideanLattice ι :=
  Equiv.ofBijective (standardEuclideanPoint ι) (standardEuclideanPoint_bijective ι)

theorem standardEuclideanLattice_self_dual :
    euclideanDualLattice (standardEuclideanLattice ι) = standardEuclideanLattice ι := by
  ext x
  rw [mem_euclideanDualLattice, mem_standardEuclideanLattice]
  constructor
  · intro hx i
    have hi : EuclideanSpace.basisFun ι ℝ i ∈ standardEuclideanLattice ι :=
      Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hx _ hi
    exact ⟨n, by simpa only [EuclideanSpace.inner_basisFun_real] using hn.symm⟩
  · intro hx y hy
    choose a ha using hx
    choose b hb using (mem_standardEuclideanLattice ι y).mp hy
    refine ⟨∑ i, a i * b i, ?_⟩
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp only [Int.cast_sum, Int.cast_mul, ha, hb]
    apply Finset.sum_congr rfl
    intro i _
    ring

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalLatticeProjection (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Λ →ₗ[ℤ] orthogonalLatticeImage Λ W :=
  ((W.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ).comp Λ.subtype).codRestrict
    (orthogonalLatticeImage Λ W) (fun x => ⟨x.val, x.property, rfl⟩)

theorem orthogonalLatticeProjection_surjective (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Function.Surjective (orthogonalLatticeProjection Λ W) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def orthogonalLatticeKernelEquiv (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    latticeSection Λ Wᗮ ≃ₗ[ℤ] LinearMap.ker (orthogonalLatticeProjection Λ W) where
  toFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext
    (W.orthogonalProjectionOnto_eq_zero_iff.mpr x.val.property)⟩
  invFun x := ⟨⟨x.val.val, W.orthogonalProjectionOnto_eq_zero_iff.mp
    (congrArg Subtype.val (show orthogonalLatticeProjection Λ W x.val = 0 from x.property))⟩,
    x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_orthogonal_lattice_split_basis {I J : Type*}
    (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bK : Basis I ℤ (latticeSection Λ Wᗮ)) (bP : Basis J ℤ (orthogonalLatticeImage Λ W)) :
    ∃ b : Basis (I ⊕ J) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, W.orthogonalProjectionOnto (b (Sum.inr j) : E) = (bP j).val) := by
  let : Free ℤ (orthogonalLatticeImage Λ W) := Free.of_basis bP
  obtain ⟨b, hK, hP⟩ := exists_basis_of_surjection (orthogonalLatticeProjection Λ W)
    (orthogonalLatticeProjection_surjective Λ W) (bK.map (orthogonalLatticeKernelEquiv Λ W)) bP
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hK]
    rfl
  · intro j
    exact congrArg Subtype.val (hP j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integerBasisOfReal (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) : Basis I ℤ Λ :=
  (b.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ hb)

theorem integerBasisOfReal_apply (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (i : I) : (integerBasisOfReal Λ b hb i).val = b i := by
  simp only [integerBasisOfReal, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply]

theorem integerBasisOfReal_synthesis [Fintype I] (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) :
    ((integerBasisOfReal Λ b hb).equivFun.symm z).val =
      b.equivFun.symm (fun i => (z i : ℝ)) := by
  simp only [integerBasisOfReal, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact latticeBasisEquiv_synthesis (span ℤ (Set.range b)) b rfl z

noncomputable def standardEuclideanLinearEquiv (J : Type*) [Fintype J] :
    (J → ℤ) ≃ₗ[ℤ] standardEuclideanLattice J :=
  ((EuclideanSpace.basisFun J ℝ).toBasis.restrictScalars ℤ).equivFun.symm

theorem standardEuclideanLinearEquiv_apply (J : Type*) [Fintype J] (z : J → ℤ) (i : J) :
    (standardEuclideanLinearEquiv J z).val i = (z i : ℝ) := by
  have h := latticeBasisEquiv_coordinates (standardEuclideanLattice J)
    (EuclideanSpace.basisFun J ℝ).toBasis rfl z i
  have he : (latticeBasisEquiv (standardEuclideanLattice J)
      (EuclideanSpace.basisFun J ℝ).toBasis rfl z).val =
      (standardEuclideanLinearEquiv J z).val := rfl
  rw [he] at h
  simpa only [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using h

theorem standardEuclideanLinearEquiv_eq_point (J : Type*) [Fintype J] (z : J → ℤ) :
    standardEuclideanLinearEquiv J z = standardEuclideanPoint J z := by
  apply Subtype.ext
  ext i
  exact standardEuclideanLinearEquiv_apply J z i

end Erdos3

end

section

namespace Erdos3

variable (J : Type*) [Fintype J]

def standardLatticeSmallBox : Set (EuclideanSpace ℝ J) :=
  {x | ∀ i, |x i| < 1 / 2}

theorem standardLatticeSmallBox_isOpen : IsOpen (standardLatticeSmallBox J) := by
  unfold standardLatticeSmallBox
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem standardLatticeSmallBox_separates
    {x y : EuclideanSpace ℝ J} (hx : x ∈ standardLatticeSmallBox J)
    (hy : y ∈ standardLatticeSmallBox J) (hxy : x - y ∈ standardEuclideanLattice J) : x = y := by
  ext i
  obtain ⟨n, hn⟩ := (mem_standardEuclideanLattice J (x - y)).mp hxy i
  change (n : ℝ) = x i - y i at hn
  have hxi := abs_lt.mp (hx i)
  have hyi := abs_lt.mp (hy i)
  have hnlo : (-1 : ℝ) < n := by linarith
  have hnhi : (n : ℝ) < 1 := by linarith
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  exact sub_eq_zero.mp (by simpa only [hn0, Int.cast_zero] using hn.symm)

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalSectionKernelEquiv (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    latticeSection Λ W ≃ₗ[ℤ] LinearMap.ker (orthogonalLatticeProjection Λ Wᗮ) where
  toFun x := ⟨⟨x.val.val, x.property⟩,
    Subtype.ext (W.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.val.property)⟩
  invFun x := ⟨⟨x.val.val, by
    have h := Wᗮ.orthogonalProjectionOnto_eq_zero_iff.mp
      (congrArg Subtype.val (show orthogonalLatticeProjection Λ Wᗮ x.val = 0 from x.property))
    change x.val.val ∈ Wᗮᗮ at h
    rwa [W.orthogonal_orthogonal] at h⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def latticeLiftSection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) :
    orthogonalLatticeImage Λ Wᗮ →ₗ[ℤ] Λ :=
  basisSurjectionSection (orthogonalLatticeProjection Λ Wᗮ)
    (orthogonalLatticeProjection_surjective Λ Wᗮ) bP

theorem latticeLiftSection_rightInverse (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : orthogonalLatticeImage Λ Wᗮ) :
    orthogonalLatticeProjection Λ Wᗮ (latticeLiftSection Λ W bP x) = x :=
  basisSurjectionSection_rightInverse _ _ _ _

variable [Fintype I] [Fintype J]

noncomputable def latticeIntegerLift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) : (J → ℤ) →ₗ[ℤ] Λ :=
  (latticeLiftSection Λ W bP).comp bP.equivFun.symm.toLinearMap

theorem latticeIntegerLift_projection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (z : J → ℤ) :
    Wᗮ.orthogonalProjectionOnto (latticeIntegerLift Λ W bP z).val = (bP.equivFun.symm z).val :=
  congrArg Subtype.val (latticeLiftSection_rightInverse Λ W bP (bP.equivFun.symm z))

noncomputable def latticeSignedCoordinates (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) :
    Λ ≃ₗ[ℤ] (J → ℤ) × (I → ℤ) :=
  signedSplitCoordinates (orthogonalLatticeProjection Λ Wᗮ) (latticeLiftSection Λ W bP)
    (latticeLiftSection_rightInverse Λ W bP) (bW.map (orthogonalSectionKernelEquiv Λ W)) bP

theorem latticeSignedCoordinates_fst (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : Λ) :
    (latticeSignedCoordinates Λ W bW bP x).1 =
      -(bP.equivFun (orthogonalLatticeProjection Λ Wᗮ x)) := rfl

theorem latticeSignedCoordinates_symm_apply (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ))
    (z : J → ℤ) (w : I → ℤ) :
    ((latticeSignedCoordinates Λ W bW bP).symm (z, w)).val =
      (bW.equivFun.symm w).val.val - (latticeIntegerLift Λ W bP z).val := by
  rw [latticeSignedCoordinates, signedSplitCoordinates_symm_apply]
  simp only [Submodule.coe_sub, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rfl

theorem latticeSignedCoordinates_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : Λ) :
    x.val + (latticeIntegerLift Λ W bP (latticeSignedCoordinates Λ W bW bP x).1).val =
      (bW.equivFun.symm (latticeSignedCoordinates Λ W bW bP x).2).val.val := by
  have h := latticeSignedCoordinates_symm_apply Λ W bW bP
    (latticeSignedCoordinates Λ W bW bP x).1 (latticeSignedCoordinates Λ W bW bP x).2
  change ((latticeSignedCoordinates Λ W bW bP).symm (latticeSignedCoordinates Λ W bW bP x)).val = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact eq_sub_iff_add_eq.mp h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def projectedLatticeLift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) : Λ :=
  (orthogonalLatticeProjection_surjective Λ Wᗮ z).choose

theorem projectedLatticeLift_projection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) :
    Wᗮ.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val = z.val :=
  congrArg Subtype.val (orthogonalLatticeProjection_surjective Λ Wᗮ z).choose_spec

noncomputable def latticeSheetPoint (W : Submodule ℝ E) (z : Wᗮ) (u : W) : E :=
  u.val + z.val

theorem latticeSheetPoint_projection (W : Submodule ℝ E) (z : Wᗮ) (u : W) :
    W.orthogonalProjectionOnto (latticeSheetPoint W z u) = u := by
  change W.orthogonalProjectionOnto (u.val + z.val) = u
  rw [map_add, W.orthogonalProjectionOnto_apply_of_mem_orthogonal z.property, add_zero]
  exact Subtype.ext (W.starProjection_eq_self_iff.mpr u.property)

theorem latticeSheetPoint_projection_orthogonal (W : Submodule ℝ E) (z : Wᗮ) (u : W) :
    Wᗮ.orthogonalProjectionOnto (latticeSheetPoint W z u) = z := by
  change Wᗮ.orthogonalProjectionOnto (u.val + z.val) = z
  rw [map_add, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero u.property, zero_add]
  exact Subtype.ext (Wᗮ.starProjection_eq_self_iff.mpr z.property)

noncomputable def projectedLatticeShift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) : W :=
  W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val

noncomputable def latticeSheetQuotient (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) (u : W) : W ⧸ (latticeSection Λ W).toAddSubgroup :=
  QuotientAddGroup.mk (u - projectedLatticeShift Λ W z)

theorem latticeSheetPoint_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) (u : W) :
    latticeSheetPoint W z.val u =
      (u - projectedLatticeShift Λ W z).val + (projectedLatticeLift Λ W z).val := by
  have hs := W.starProjection_add_starProjection_orthogonal (projectedLatticeLift Λ W z).val
  change (projectedLatticeShift Λ W z).val +
    (Wᗮ.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val = _ at hs
  rw [projectedLatticeLift_projection] at hs
  change u.val + z.val.val = (u.val - (projectedLatticeShift Λ W z).val) + _
  calc
    _ = (u.val - (projectedLatticeShift Λ W z).val) +
        ((projectedLatticeShift Λ W z).val + z.val.val) := by abel
    _ = _ := by rw [hs]

theorem latticeSheetPoint_sub_mem_of_quotient_eq (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    {z w : orthogonalLatticeImage Λ Wᗮ} {u v : W}
    (h : latticeSheetQuotient Λ W z u = latticeSheetQuotient Λ W w v) :
    latticeSheetPoint W z.val u - latticeSheetPoint W w.val v ∈ Λ := by
  have hm := QuotientAddGroup.eq_iff_sub_mem.mp h
  change ((u - projectedLatticeShift Λ W z) - (v - projectedLatticeShift Λ W w)).val ∈ Λ at hm
  have hl := Λ.sub_mem (projectedLatticeLift Λ W z).property (projectedLatticeLift Λ W w).property
  rw [latticeSheetPoint_reconstruction, latticeSheetPoint_reconstruction]
  convert Λ.add_mem hm hl using 1
  simp only [Submodule.coe_sub]
  abel

theorem latticeSheetQuotient_injective_on_region (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    {Ω : Set E}
    (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, x - y ∈ Λ → x = y)
    {z w : orthogonalLatticeImage Λ Wᗮ} {u v : W}
    (hu : latticeSheetPoint W z.val u ∈ Ω) (hv : latticeSheetPoint W w.val v ∈ Ω)
    (h : latticeSheetQuotient Λ W z u = latticeSheetQuotient Λ W w v) : z = w ∧ u = v := by
  have he := hΩ _ hu _ hv (latticeSheetPoint_sub_mem_of_quotient_eq Λ W h)
  constructor
  · apply Subtype.ext
    simpa only [latticeSheetPoint_projection_orthogonal] using
      congrArg Wᗮ.orthogonalProjectionOnto he
  · simpa only [latticeSheetPoint_projection] using congrArg W.orthogonalProjectionOnto he

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open MeasureTheory

theorem normalizedLatticeSheet_point {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (Λ : Submodule ℤ Wᗮ) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = Λ) (z : Fin n → ℤ) (u : W) :
    latticeSheetPoint W (latticeBasisEquiv Λ b hb z).val u =
      (normalizedOrthogonalChart W b).symm (u, fun i => (z i : ℝ) / (basisAxisScale b i : ℝ)) := by
  apply (normalizedOrthogonalChart W b).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, normalizedOrthogonalChart_apply,
    latticeSheetPoint_projection, latticeSheetPoint_projection_orthogonal]
  refine Prod.ext rfl ?_
  funext i
  change b.equivFun (latticeBasisEquiv Λ b hb z).val i / (basisAxisScale b i : ℝ) =
    (z i : ℝ) / (basisAxisScale b i : ℝ)
  rw [latticeBasisEquiv_coordinates]

theorem normalizedLatticeSheet_tsum_volume {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℝ E) (Λ : Submodule ℤ Wᗮ) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = Λ) (Ω : Set E) :
    (∑' z : Λ, volume {u : W | latticeSheetPoint W z.val u ∈ Ω}) =
      ∑' z : Fin n → ℤ, volume {u : W |
        (normalizedOrthogonalChart W b).symm
          (u, fun i => (z i : ℝ) / (basisAxisScale b i : ℝ)) ∈ Ω} := by
  have h := (latticeBasisEquiv Λ b hb).tsum_eq
    (fun z => volume {u : W | latticeSheetPoint W z.val u ∈ Ω})
  simp_rw [normalizedLatticeSheet_point W Λ b hb] at h
  exact h.symm

end Erdos3

end

end OAI
