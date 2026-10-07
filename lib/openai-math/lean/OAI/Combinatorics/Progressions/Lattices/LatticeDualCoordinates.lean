import OAI.Combinatorics.Progressions.Fourier.MonomialCharacterMean

namespace OAI

section

namespace Erdos3

open Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeDualBasis (b : Basis ι ℤ Λ) : Basis ι ℝ E := by
  classical
  exact LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate (b.ofZLatticeBasis ℝ Λ)

theorem euclideanDualLattice_eq_span (b : Basis ι ℤ Λ) :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range (latticeDualBasis Λ b)) := by
  classical
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E)
    realInner_nondegenerate (b.ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, latticeDualBasis, Basis.ofZLatticeBasis_span] using h

noncomputable def latticeDualPoint (b : Basis ι ℤ Λ) (n : ι → ℤ) : E :=
  (latticeDualBasis Λ b).equivFun.symm (fun i => (n i : ℝ))

@[simp]
theorem latticeDualPoint_neg (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    latticeDualPoint Λ b (-n) = -latticeDualPoint Λ b n := by
  simp only [latticeDualPoint, Pi.neg_apply, Int.cast_neg]
  change (latticeDualBasis Λ b).equivFun.symm (-(fun i => (n i : ℝ))) = _
  exact map_neg _ _

theorem latticeDualPoint_inner_basis (b : Basis ι ℤ Λ) (n : ι → ℤ) (i : ι) :
    inner ℝ (latticeDualPoint Λ b n) (b.ofZLatticeBasis ℝ Λ i) = (n i : ℝ) := by
  have h := congrFun ((latticeDualBasis Λ b).equivFun.apply_symm_apply (fun j => (n j : ℝ))) i
  simpa only [Basis.equivFun_apply, latticeDualBasis, latticeDualPoint,
    LinearMap.BilinForm.dualBasis_repr_apply, innerₗ_apply_apply] using h

theorem latticeDualPoint_mem (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    latticeDualPoint Λ b n ∈ euclideanDualLattice Λ := by
  rw [euclideanDualLattice_eq_span Λ b, (latticeDualBasis Λ b).mem_span_iff_repr_mem ℤ]
  intro i
  refine ⟨n i, ?_⟩
  have h := congrFun ((latticeDualBasis Λ b).equivFun.apply_symm_apply (fun j => (n j : ℝ))) i
  exact h.symm

theorem latticeDualPoint_injective (b : Basis ι ℤ Λ) : Function.Injective (latticeDualPoint Λ b) := by
  intro n m h
  have he := congrArg (latticeDualBasis Λ b).equivFun h
  simp only [latticeDualPoint, LinearEquiv.apply_symm_apply] at he
  ext i
  exact Int.cast_injective (congrFun he i)

theorem latticeDualPoint_surjective (b : Basis ι ℤ Λ) (ξ : euclideanDualLattice Λ) :
    ∃ n : ι → ℤ, latticeDualPoint Λ b n = ξ := by
  classical
  have hmem := ((latticeDualBasis Λ b).mem_span_iff_repr_mem ℤ (ξ : E)).mp
    ((euclideanDualLattice_eq_span Λ b).le ξ.property)
  choose n hn using hmem
  refine ⟨n, ?_⟩
  apply (latticeDualBasis Λ b).equivFun.injective
  ext i
  change (latticeDualBasis Λ b).equivFun
    ((latticeDualBasis Λ b).equivFun.symm (fun j => (n j : ℝ))) i = _
  rw [LinearEquiv.apply_symm_apply]
  exact hn i

noncomputable def latticeDualEquiv (b : Basis ι ℤ Λ) : (ι → ℤ) ≃ euclideanDualLattice Λ :=
  Equiv.ofBijective (fun n => ⟨latticeDualPoint Λ b n, latticeDualPoint_mem Λ b n⟩)
    ⟨fun _ _ h => latticeDualPoint_injective Λ b (congrArg Subtype.val h), fun ξ => by
      obtain ⟨n, hn⟩ := latticeDualPoint_surjective Λ b ξ
      exact ⟨n, Subtype.ext hn⟩⟩

@[simp]
theorem latticeDualEquiv_coe (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    ((latticeDualEquiv Λ b n : euclideanDualLattice Λ) : E) = latticeDualPoint Λ b n := rfl

theorem latticeDualPoint_inner_coordinates (b : Basis ι ℤ Λ) (n : ι → ℤ) (x : ι → ℝ) :
    inner ℝ (latticeDualPoint Λ b n) ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) =
      ∑ i, (n i : ℝ) * x i := by
  rw [Basis.equivFun_symm_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right, latticeDualPoint_inner_basis, mul_comm]

theorem latticeDualPoint_character (b : Basis ι ℤ Λ) (n : ι → ℤ) (x : ι → ℝ) :
    euclideanCharacter (latticeDualPoint Λ b n) ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) =
      UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle)) := by
  rw [euclideanCharacter_eq_exp, latticeDualPoint_inner_coordinates]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum,
    UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  congr 1
  ring

end Erdos3

end

end OAI
