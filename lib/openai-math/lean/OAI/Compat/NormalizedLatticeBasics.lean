/-
Modified for ProveIt: Extract the basic lattice declarations from the port of
OAI/Combinatorics/Progressions/Lattices/NormalizedLatticeSheet.lean in
https://github.com/openai/math, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The ported declaration types and proof bodies are unchanged. The original
module re-exports this extract. Omit the geometric sheet imports so recurrence
consumers can use lattice basics independently of the sheet construction.
Distributed under Apache-2.0; see ../../../LICENSE and LICENSE.provenance
in lib/openai-math. Upstream copyright status is recorded there.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Estimates.GaussianScaledShortVectorBound
import OAI.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection

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

end OAI
