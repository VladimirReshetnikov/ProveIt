/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_joint_injective :
    Function.Injective (fun x : (pi D).Space => fun i => productProjection D i x) := by
  intro x y h
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    apply QuotientGroup.eq.mpr
    change x⁻¹ * y ∈ (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)).map realificationHom
    rw [realBCHPiEquiv_mem_lattice]
    intro i
    have hi := congrFun h i
    have hmem := QuotientGroup.eq.mp hi
    change productProjectionHom D i (x⁻¹ * y) ∈ (D i).realLattice
    simpa only [map_mul, map_inv] using hmem

theorem productProjection_joint_surjective :
    Function.Surjective (fun x : (pi D).Space => fun i => productProjection D i x) := by
  intro y
  let F := fun i => (D i).filtration
  let g := (realBCHPiEquiv F).symm (fun i => (y i).out)
  refine ⟨QuotientGroup.mk g, ?_⟩
  funext i
  change QuotientGroup.mk (realBCHPiEquiv F g i) = y i
  rw [show realBCHPiEquiv F g = (fun i => (y i).out) from (realBCHPiEquiv F).apply_symm_apply _]
  exact Quotient.out_eq (y i)

noncomputable def productSpaceEquiv : (pi D).Space ≃ (∀ i, (D i).Space) :=
  Equiv.ofBijective (fun x i => productProjection D i x)
    ⟨productProjection_joint_injective D, productProjection_joint_surjective D⟩

@[simp] theorem productSpaceEquiv_apply (x : (pi D).Space) (i : ι) :
    productSpaceEquiv D x i = productProjection D i x := rfl

@[simp] theorem productSpaceEquiv_mk (g : (pi D).RealGroup) (i : ι) :
    productSpaceEquiv D (QuotientGroup.mk g) i = QuotientGroup.mk (productProjectionHom D i g) := rfl

theorem productSpaceEquiv_symm_mk (g : ∀ i, (D i).RealGroup) :
    (productSpaceEquiv D).symm (fun i => QuotientGroup.mk (g i)) =
      QuotientGroup.mk ((realBCHPiEquiv (fun i => (D i).filtration)).symm g) := by
  apply (productSpaceEquiv D).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change QuotientGroup.mk (g i) = QuotientGroup.mk
    (realBCHPiEquiv (fun i => (D i).filtration)
      ((realBCHPiEquiv (fun i => (D i).filtration)).symm g) i)
  rw [MulEquiv.apply_symm_apply]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realification_piRight_symm_single (i : ι) (x : ℝ ⊗[ℚ] L i) :
    (TensorProduct.piRight ℚ ℝ ℝ L).symm (Pi.single i x) =
      realificationLieHom (liePiSingle i) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [TensorProduct.piRight_symm_single]
    rfl
  | add x y hx hy => simp only [Pi.single_add, map_add, hx, hy]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productInclusionHom (i : ι) : (D i).RealGroup →* (pi D).RealGroup :=
  realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
    (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiSingle i)

theorem realBCHPiEquiv_symm_single (i : ι) (g : (D i).RealGroup) :
    (realBCHPiEquiv (fun i => (D i).filtration)).symm (Pi.mulSingle i g) = productInclusionHom D i g := by
  apply NilpotentLieBCHGroup.ext
  change (TensorProduct.piRight ℚ ℝ ℝ L).symm
    (fun j => ((Pi.mulSingle i g : ∀ j, (D j).RealGroup) j).coord) =
    realificationLieHom (liePiSingle i) g.coord
  have h : (fun j => ((Pi.mulSingle i g : ∀ j, (D j).RealGroup) j).coord) = Pi.single i g.coord := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    · simp only [Pi.mulSingle_eq_of_ne hji, Pi.single_eq_of_ne hji, coord_one]
  rw [h, realification_piRight_symm_single]

theorem productInclusion_matrix_height (i : ι) (j : Fin (d i))
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    RationalHeightLE ((pi D).basis.repr (liePiSingle i ((D i).basis j)) k) 1 := by
  change RationalHeightLE ((pi D).basis.repr (Pi.single i ((D i).basis j)) k) 1
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i, Fin (d i))).symm k = z
  rcases z with ⟨a, l⟩
  by_cases hai : a = i
  · subst a
    rw [Pi.single_eq_same, Module.Basis.repr_self]
    by_cases hjl : j = l <;> simp [hjl, RationalHeightLE]
  · rw [Pi.single_eq_of_ne hai, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

theorem productSpaceEquiv_symm_update_mk (g : ∀ i, (D i).RealGroup) (i : ι) (a : (D i).RealGroup) :
    (productSpaceEquiv D).symm (Function.update (fun j => QuotientGroup.mk (g j)) i (QuotientGroup.mk a)) =
      QuotientGroup.mk ((realBCHPiEquiv (fun j => (D j).filtration)).symm (Function.update g i a)) := by
  have h : Function.update (fun j => (QuotientGroup.mk (g j) : (D j).Space)) i (QuotientGroup.mk a) =
      (fun j => QuotientGroup.mk (Function.update g i a j)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
  rw [h, productSpaceEquiv_symm_mk]

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
