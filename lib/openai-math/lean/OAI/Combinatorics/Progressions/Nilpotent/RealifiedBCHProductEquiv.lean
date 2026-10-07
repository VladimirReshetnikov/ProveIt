/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import OAI.Combinatorics.Progressions.Estimates.ControlledProductReconstruction

namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

theorem realification_piRight_apply (x : ℝ ⊗[ℚ] (∀ i, L i)) (i : ι) :
    TensorProduct.piRight ℚ ℝ ℝ L x i = realificationLieHom (liePiEval i) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

noncomputable def realBCHPiEquiv (F : ∀ i, NilpotentLieFiltration (L i) s) :
    (NilpotentLieFiltration.pi F).realification.Group ≃* (∀ i, (F i).realification.Group) where
  toFun g i := realificationMap (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
    (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i) g
  invFun g := ⟨(TensorProduct.piRight ℚ ℝ ℝ L).symm (fun i => (g i).coord)⟩
  left_inv g := by
    apply NilpotentLieBCHGroup.ext
    change (TensorProduct.piRight ℚ ℝ ℝ L).symm
      (fun i => realificationLieHom (liePiEval i) g.coord) = g.coord
    have h : (fun i => realificationLieHom (liePiEval i) g.coord) =
        TensorProduct.piRight ℚ ℝ ℝ L g.coord := funext (fun i => (realification_piRight_apply g.coord i).symm)
    rw [h, LinearEquiv.symm_apply_apply]
  right_inv g := by
    funext i
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval i)
      ((TensorProduct.piRight ℚ ℝ ℝ L).symm (fun i => (g i).coord)) = (g i).coord
    rw [← realification_piRight_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    funext i
    exact (realificationMap (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
      (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)).map_mul g h

theorem realBCHPiEquiv_mem_lattice (F : ∀ i, NilpotentLieFiltration (L i) s)
    (Γ : ∀ i, Subgroup (F i).Group) (g : (NilpotentLieFiltration.pi F).realification.Group) :
    g ∈ (piBCHSubgroup F Γ).map realificationHom ↔
      ∀ i, realBCHPiEquiv F g i ∈ (Γ i).map realificationHom := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨⟨x.coord i⟩, (mem_piBCHSubgroup F Γ x).mp hx i, rfl⟩
  · intro h
    choose x hx heq using h
    let y : (NilpotentLieFiltration.pi F).Group := ⟨fun i => (x i).coord⟩
    refine Subgroup.mem_map.mpr ⟨y, (mem_piBCHSubgroup F Γ y).mpr hx, ?_⟩
    apply (realBCHPiEquiv F).injective
    funext i
    exact heq i

end Erdos3

end

end OAI
