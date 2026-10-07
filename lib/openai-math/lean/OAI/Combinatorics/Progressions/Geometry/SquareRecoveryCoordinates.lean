/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

omit [DecidableEq ι] in
theorem realProductFinBasis_repr (x : ℝ ⊗[ℚ] (∀ i, L i))
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    ((pi D).basis.baseChange ℝ).repr x k =
      ((D z.1).basis.baseChange ℝ).repr (realificationLieHom (liePiEval z.1) x) z.2 := by
  dsimp only
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [Basis.baseChange_repr_tmul, realificationLieHom_tmul,
      productFinBasis_repr D, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

@[simp] theorem productProjectionHom_pi_symm (g : ∀ i, (D i).RealGroup) (i : ι) :
    productProjectionHom D i ((realBCHPiEquiv (fun j => (D j).filtration)).symm g) = g i :=
  congrFun ((realBCHPiEquiv (fun j => (D j).filtration)).apply_symm_apply g) i

theorem realProductFinBasis_pi_symm_bound (g : ∀ i, (D i).RealGroup) {R : ℝ}
    (hg : ∀ i j, |((D i).basis.baseChange ℝ).repr (g i).coord j| ≤ R)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    |((pi D).basis.baseChange ℝ).repr
      ((realBCHPiEquiv (fun i => (D i).filtration)).symm g).coord k| ≤ R := by
  rw [realProductFinBasis_repr D]
  let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
  change |((D z.1).basis.baseChange ℝ).repr
    (productProjectionHom D z.1 ((realBCHPiEquiv (fun i => (D i).filtration)).symm g)).coord z.2| ≤ R
  rw [productProjectionHom_pi_symm]
  exact hg z.1 z.2

theorem pi_symm_mem_realLattice (g : ∀ i, (D i).RealGroup)
    (hg : ∀ i, g i ∈ (D i).realLattice) :
    (realBCHPiEquiv (fun i => (D i).filtration)).symm g ∈ (pi D).realLattice := by
  apply (realBCHPiEquiv_mem_lattice (fun i => (D i).filtration)
    (fun i => (D i).lattice) _).mpr
  intro i
  rw [MulEquiv.apply_symm_apply]
  change g i ∈ (D i).realLattice
  exact hg i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem squarePairMap_matrix_logHeight (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : D.filtration.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {p : ℝ} (hp : 0 ≤ p) (hb : ∀ i j, rationalLogHeight (D.basis.repr (b j) i) ≤ p)
    (i : Fin (Fintype.card (Σ _ : Bool, Fin d)))
    (j : Fin (Fintype.card (κ ⊕ {i // 2 ≤ w i}))) :
    rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
      (D.filtration.squarePairMap (D.filtration.squareFinBasis b w h j)) i) ≤ p + 1 := by
  rw [productFinBasis_repr]
  let z := (Fintype.equivFin (Σ _ : Bool, Fin d)).symm i
  have H := D.filtration.squareFinBasis_projection_height D.basis b w h
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hb i j)) j z.2
  apply rationalLogHeight_le_of_height _ (ceil_exp_le_exp_add_one hp)
  change RationalHeightLE (D.basis.repr
    (D.filtration.squarePairMap (D.filtration.squareFinBasis b w h j) z.1) z.2) _
  cases hz : z.1
  · exact H.2
  · exact H.1

omit [Fintype κ] in
theorem squareNormalizer_coordinate_bound (ε : D.RealGroup) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ R)
    (j : Fin (Fintype.card (Σ _ : Bool, Fin d))) :
    |((pi (fun _ : Bool => D)).basis.baseChange ℝ).repr
      ((realBCHPiEquiv (fun _ : Bool => D.filtration)).symm
        (fun flag => cond flag ε⁻¹ 1)).coord j| ≤ R := by
  apply realProductFinBasis_pi_symm_bound
  intro flag i
  cases flag
  · simpa only [Bool.cond_false, coord_one, map_zero, Finsupp.zero_apply, abs_zero] using hR
  · simpa only [Bool.cond_true, coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hε i

end Erdos3.RationalFilteredNilmanifold

end

end OAI
