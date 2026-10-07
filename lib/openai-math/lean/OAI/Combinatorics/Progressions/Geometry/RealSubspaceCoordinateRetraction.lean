import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Basis
import OAI.Combinatorics.Progressions.Linear.QuotientActionMatrix
import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
import OAI.Combinatorics.Progressions.Polynomial.SubspacePolynomialCoordinates

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_matrix_right_inverse {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (hDS : D * S = 1) :
    D.map (Rat.castHom ℝ) * S.map (Rat.castHom ℝ) = 1 := by
  rw [← Matrix.map_mul, hDS]
  exact Matrix.map_one _ (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℝ W]
  (U : Submodule ℚ V)

theorem realification_mkQ_ker : LinearMap.ker (U.mkQ.baseChange ℝ) = U.baseChange ℝ := by
  rw [← realification_ker, Submodule.ker_mkQ]

theorem realification_mkQ_surjective : Function.Surjective (U.mkQ.baseChange ℝ) :=
  LinearMap.lTensor_surjective ℝ U.mkQ_surjective

noncomputable def realQuotientEquiv :
    (ℝ ⊗[ℚ] (V ⧸ U)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] V) ⧸ U.baseChange ℝ) :=
  (U.mkQ.baseChange ℝ).quotKerEquivOfSurjective
    (realification_mkQ_surjective U) |>.symm |>.trans
      (Submodule.quotEquivOfEq _ _ (realification_mkQ_ker U))

theorem realQuotientEquiv_mk (x : ℝ ⊗[ℚ] V) :
    realQuotientEquiv U (U.mkQ.baseChange ℝ x) = (U.baseChange ℝ).mkQ x := by
  dsimp only [realQuotientEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

noncomputable def realTransportedQuotientEquiv (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) :
    (ℝ ⊗[ℚ] (V ⧸ U)) ≃ₗ[ℝ] (W ⧸ (U.baseChange ℝ).map E.toLinearMap) :=
  (realQuotientEquiv U).trans (Submodule.Quotient.equiv _ _ E rfl)

theorem realTransportedQuotientEquiv_mk (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (x : ℝ ⊗[ℚ] V) :
    realTransportedQuotientEquiv U E (U.mkQ.baseChange ℝ x) =
      ((U.baseChange ℝ).map E.toLinearMap).mkQ (E x) := by
  change Submodule.Quotient.equiv _ _ E rfl (realQuotientEquiv U (U.mkQ.baseChange ℝ x)) = _
  rw [realQuotientEquiv_mk]
  rfl

noncomputable def realTransportedQuotientBasis {κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (b : Basis κ ℚ (V ⧸ U)) :
    Basis κ ℝ (W ⧸ (U.baseChange ℝ).map E.toLinearMap) :=
  (b.baseChange ℝ).map (realTransportedQuotientEquiv U E)

theorem realTransportedQuotientBasis_repr_mk {κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (b : Basis κ ℚ (V ⧸ U)) (x : ℝ ⊗[ℚ] V) (i : κ) :
    (realTransportedQuotientBasis U E b).repr
      (((U.baseChange ℝ).map E.toLinearMap).mkQ (E x)) i =
      (b.baseChange ℝ).repr (U.mkQ.baseChange ℝ x) i := by
  rw [← realTransportedQuotientEquiv_mk]
  simp only [realTransportedQuotientBasis, Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem realTransportedQuotientBasis_repr_basis {ι κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (e : Basis ι ℚ V) (b : Basis κ ℚ (V ⧸ U)) (i : ι) (j : κ) :
    (realTransportedQuotientBasis U E b).repr
      (((U.baseChange ℝ).map E.toLinearMap).mkQ (E ((e.baseChange ℝ) i))) j =
      (b.repr (U.mkQ (e i)) j : ℝ) := by
  rw [realTransportedQuotientBasis_repr_mk]
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix NNReal

variable {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
  (D : Matrix κ ι ℚ) (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))

include hD

theorem rational_coordinate_map (x : V) :
    f.equivFun (q x) = D.map (Rat.castHom ℝ) *ᵥ e.equivFun x := by
  have h := LinearMap.toMatrix_mulVec_repr e f q x
  rw [hD] at h
  exact h.symm

theorem rational_coordinate_map_grid (l : ℕ) (x : V)
    (hx : e.equivFun x ∈ realDenominatorGrid l) :
    f.equivFun (q x) ∈ realDenominatorGrid (matrixDenominator D * l) := by
  rw [rational_coordinate_map e f q D hD]
  exact real_matrix_denominator_grid D l _ hx

theorem rational_coordinate_map_weighted (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, r i ≠ c j → D i j = 0)
    (H : ℝ≥0) (hH : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ H)
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (x : V) (hx : ∀ j, |e.equivFun x j| ≤ M / scale (c j)) (i : κ) :
    |f.equivFun (q x) i| ≤
      ((Fintype.card ι : ℝ) + 1) * (H + 1) * M / scale (r i) := by
  rw [rational_coordinate_map e f q D hD]
  exact weighted_matrix_mulVec_bound r c (D.map (Rat.castHom ℝ))
    (fun i j h => by change (D i j : ℝ) = 0; rw [hblock i j h, Rat.cast_zero])
    H (fun i j => (rational_abs_real_le_numerator (D i j)).trans (hH i j))
    scale hscale hM (e.equivFun x) hx i

theorem rational_coordinate_map_weighted_exp (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, r i ≠ c j → D i j = 0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hH : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (x : V) (hx : ∀ j, |e.equivFun x j| ≤ M / scale (c j)) (i : κ) :
    |f.equivFun (q x) i| ≤ Real.exp ((p + 2) ^ (a + 2)) * M / scale (r i) := by
  have h := rational_coordinate_map_weighted e f q D hD c r hblock
    ⟨Real.exp ((p + 2) ^ a), Real.exp_nonneg _⟩ hH scale hscale hM x hx i
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (matrix_weighted_factor_le_exp_power _ hp hι a ha) hM)
    (hscale _).le)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ δ V : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (S : Matrix ι κ ℚ)

noncomputable def rationalCoordinateSection : (κ → ℝ) →ₗ[ℝ] V :=
  e.equivFun.symm.toLinearMap.comp (S.map (Rat.castHom ℝ)).mulVecLin

theorem rationalCoordinateSection_coordinates (y : κ → ℝ) :
    e.equivFun (rationalCoordinateSection e S y) = S.map (Rat.castHom ℝ) *ᵥ y :=
  e.equivFun.apply_symm_apply _

theorem rationalCoordinateSection_grid (l : ℕ) (y : κ → ℝ)
    (hy : y ∈ realDenominatorGrid l) :
    e.equivFun (rationalCoordinateSection e S y) ∈
      realDenominatorGrid (matrixDenominator S * l) := by
  rw [rationalCoordinateSection_coordinates]
  exact real_matrix_denominator_grid S l y hy

theorem rationalCoordinateSection_weighted (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, c i ≠ r j → S i j = 0) {p : ℝ} (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hH : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (y : κ → ℝ) (hy : ∀ j, |y j| ≤ M / scale (r j)) (i : ι) :
    |e.equivFun (rationalCoordinateSection e S y) i| ≤
      Real.exp ((p + 2) ^ (a + 2)) * M / scale (c i) := by
  rw [rationalCoordinateSection_coordinates]
  have h := weighted_matrix_mulVec_bound c r (S.map (Rat.castHom ℝ))
    (fun i j h => by change (S i j : ℝ) = 0; rw [hblock i j h, Rat.cast_zero])
    ⟨Real.exp ((p + 2) ^ a), Real.exp_nonneg _⟩
    (fun i j => (rational_abs_real_le_numerator (S i j)).trans (hH i j))
    scale hscale hM y hy i
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (matrix_weighted_factor_le_exp_power _ hp hκ a ha) hM)
    (hscale _).le)

theorem rationalCoordinateSection_rightInverse [DecidableEq ι] [DecidableEq κ]
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : Basis κ ℝ W)
    (q : V →ₗ[ℝ] W) (D : Matrix κ ι ℚ)
    (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))
    (hDS : D * S = 1) (y : κ → ℝ) :
    q (rationalCoordinateSection e S y) = f.equivFun.symm y :=
  (quotient_basis_representative e f q (D.map (Rat.castHom ℝ)) (S.map (Rat.castHom ℝ))
    hD (real_matrix_right_inverse D S hDS) y).symm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V W E : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup E] [Module ℝ E]

theorem scalarExtension_basis_coordinates (e : Basis ι ℚ V) (f : Basis κ ℚ W)
    (q : V →ₗ[ℚ] W) (i : κ) (j : ι) :
    (f.baseChange ℝ).repr (q.baseChange ℝ ((e.baseChange ℝ) j)) i =
      (f.repr (q (e j)) i : ℝ) := by
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem scalarExtension_equiv_matrix [Fintype ι] [DecidableEq ι] [Fintype κ]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (b : Basis κ ℝ E)
    (q : V →ₗ[ℚ] W) (u : (ℝ ⊗[ℚ] W) ≃ₗ[ℝ] E)
    (hu : ∀ x i, b.repr (u x) i = (f.baseChange ℝ).repr x i) :
    LinearMap.toMatrix (e.baseChange ℝ) b (u.toLinearMap.comp (q.baseChange ℝ)) =
      (LinearMap.toMatrix e f q).map (Rat.castHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    hu, scalarExtension_basis_coordinates, Matrix.map_apply, Rat.coe_castHom]

theorem scalarExtension_grid_of_height_one [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W)
    (hq : ∀ i j, RationalHeightLE (f.repr (q (e j)) i) 1)
    (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (fun i => (e.baseChange ℝ).repr x i) ∈ realDenominatorGrid l) :
    (fun i => (f.baseChange ℝ).repr (q.baseChange ℝ x) i) ∈ realDenominatorGrid l := by
  classical
  let D := LinearMap.toMatrix e f q
  have hD : LinearMap.toMatrix (e.baseChange ℝ) (f.baseChange ℝ) (q.baseChange ℝ) =
      D.map (Rat.castHom ℝ) := by
    ext i j
    simp only [D, LinearMap.toMatrix_apply, Matrix.map_apply,
      scalarExtension_basis_coordinates, Rat.coe_castHom]
  have hden : matrixDenominator D = 1 := by
    apply Nat.le_antisymm
    · have hb : ∀ i j, RationalHeightLE (D i j) 1 := by
        simpa only [D, LinearMap.toMatrix_apply] using hq
      simpa using matrixDenominator_le D hb
    · exact matrixDenominator_pos D
  have h := rational_coordinate_map_grid (e.baseChange ℝ) (f.baseChange ℝ)
    (q.baseChange ℝ) D hD l x hx
  simpa only [hden, one_mul, Basis.equivFun_apply] using h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem controlled_weighted_quotient_coordinates
    {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
    (c : ι → δ) (r : κ → δ) (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ)
    (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ)) (hDS : D * S = 1)
    (hDb : ∀ i j, r i ≠ c j → D i j = 0) (hSb : ∀ i j, c i ≠ r j → S i j = 0)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hDh : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hSh : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ (a + 4)) ∧ l ∣ m ∧
      (∀ x : V, e.equivFun x ∈ realDenominatorGrid l →
        f.equivFun (q x) ∈ realDenominatorGrid m) ∧
      (∀ y : κ → ℝ, y ∈ realDenominatorGrid l →
        e.equivFun (rationalCoordinateSection e S y) ∈ realDenominatorGrid m) ∧
      (∀ y : κ → ℝ, q (rationalCoordinateSection e S y) = f.equivFun.symm y) ∧
      ∀ (scale : δ → ℝ), (∀ d, 0 < scale d) → ∀ M : ℝ, 0 ≤ M →
        (∀ x : V, (∀ j, |e.equivFun x j| ≤ M / scale (c j)) →
          ∀ i, |f.equivFun (q x) i| ≤ Real.exp ((p + 2) ^ (a + 4)) * M / scale (r i)) ∧
        (∀ y : κ → ℝ, (∀ j, |y j| ≤ M / scale (r j)) →
          ∀ i, |e.equivFun (rationalCoordinateSection e S y) i| ≤
            Real.exp ((p + 2) ^ (a + 4)) * M / scale (c i)) := by
  let m := matrixDenominator D * matrixDenominator S * l
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos (matrixDenominator_pos D) (matrixDenominator_pos S)) hl
  have hmD : matrixDenominator D * l ∣ m := ⟨matrixDenominator S, by dsimp [m]; ring⟩
  have hmS : matrixDenominator S * l ∣ m := ⟨matrixDenominator D, by dsimp [m]; ring⟩
  refine ⟨m, hm, matrix_pair_denominator_le_exp_power D S l hp a ha hι hκ
    (fun i j => (hDh i j).2) (fun i j => (hSh i j).2) hlp,
    ⟨matrixDenominator D * matrixDenominator S, by dsimp [m]; ring⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos (matrixDenominator_pos D) hl) hmD
      (rational_coordinate_map_grid e f q D hD l x hx)
  · intro y hy
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos (matrixDenominator_pos S) hl) hmS
      (rationalCoordinateSection_grid e S l y hy)
  · exact rationalCoordinateSection_rightInverse e S f q D hD hDS
  · intro scale hscale M hM
    have hbudget : Real.exp ((p + 2) ^ (a + 2)) ≤ Real.exp ((p + 2) ^ (a + 4)) :=
      Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega))
    constructor
    · intro x hx i
      have h := rational_coordinate_map_weighted_exp e f q D hD c r hDb hp hι a ha
        (fun i j => (hDh i j).1) scale hscale hM x hx i
      exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hM) (hscale _).le)
    · intro y hy i
      have h := rationalCoordinateSection_weighted e S c r hSb hp hκ a ha
        (fun i j => (hSh i j).1) scale hscale hM y hy i
      exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hM) (hscale _).le)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem linearMap_coordinate_norm_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W) (A : ℝ≥0)
    (hentries : ∀ i j, |f.repr (q (e j)) i| ≤ A) (x : V) :
    ‖f.equivFun (q x)‖ ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have h := abs_linearMap_le_basis_bound e ((f.coord i).comp q) A (hentries i) x
  simpa only [LinearMap.comp_apply, Basis.coord_apply, Basis.equivFun_apply, Real.norm_eq_abs] using h

theorem linearMap_coordinate_dist_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W) (A : ℝ≥0)
    (hentries : ∀ i j, |f.repr (q (e j)) i| ≤ A) (x y : V) :
    dist (f.equivFun (q x)) (f.equivFun (q y)) ≤
      (Fintype.card ι : ℝ) * A * dist (e.equivFun x) (e.equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using linearMap_coordinate_norm_le e f q A hentries (x - y)

theorem scalarExtension_coordinate_norm_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W) {p : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (f.repr (q (e j)) i) ≤ p) (x : ℝ ⊗[ℚ] V) :
    ‖(f.baseChange ℝ).equivFun (q.baseChange ℝ x)‖ ≤
      Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  have h := linearMap_coordinate_norm_le (e.baseChange ℝ) (f.baseChange ℝ) (q.baseChange ℝ)
    ⟨Real.exp p, Real.exp_nonneg p⟩ (fun i j => by
      rw [scalarExtension_basis_coordinates]
      exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp (hentries i j)).1) x
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    (Fintype.card ι : ℝ) * Real.exp p ≤ Real.exp p * Real.exp p :=
      mul_le_mul_of_nonneg_right (hd.trans (by linarith [Real.add_one_le_exp p])) (Real.exp_nonneg _)
    _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring

theorem scalarExtension_coordinate_dist_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W) {p : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (f.repr (q (e j)) i) ≤ p) (x y : ℝ ⊗[ℚ] V) :
    dist ((f.baseChange ℝ).equivFun (q.baseChange ℝ x))
      ((f.baseChange ℝ).equivFun (q.baseChange ℝ y)) ≤
      Real.exp (2 * p) * dist ((e.baseChange ℝ).equivFun x) ((e.baseChange ℝ).equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using scalarExtension_coordinate_norm_le e f q hd hentries (x - y)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]

theorem realified_linear_coordinate_matrix (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) :
    LinearMap.toMatrix (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ) =
      (LinearMap.toMatrix b c φ).map (Rat.castHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply,
    scalarExtension_basis_coordinates, Rat.coe_castHom]

theorem realified_linear_coordinate_norm (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {H : ℕ}
    (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (x : ℝ ⊗[ℚ] L) :
    ‖(c.baseChange ℝ).equivFun (φ.baseChange ℝ x)‖ ≤
      ((Fintype.card ι : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [rational_coordinate_map (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ)
    (LinearMap.toMatrix b c φ) (realified_linear_coordinate_matrix b c φ)]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hφ i j).abs_real_le) _

theorem realified_linear_coordinate_grid (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (l : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (c.baseChange ℝ).equivFun (φ.baseChange ℝ x) ∈
      realDenominatorGrid (matrixDenominator (LinearMap.toMatrix b c φ) * l) := by
  exact rational_coordinate_map_grid (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ)
    (LinearMap.toMatrix b c φ) (realified_linear_coordinate_matrix b c φ) l x hx

theorem realified_section_correction_coordinate_norm [DecidableEq κ]
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ}
    (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (x : ℝ ⊗[ℚ] L) (y : ℝ ⊗[ℚ] M) :
    ‖(b.baseChange ℝ).equivFun (x - S.baseChange ℝ (φ.baseChange ℝ x - y))‖ ≤
      ‖(b.baseChange ℝ).equivFun x‖ +
        (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
          ((((Fintype.card ι : ℝ) + 1) * (H + 1)) *
            ‖(b.baseChange ℝ).equivFun x‖ + ‖(c.baseChange ℝ).equivFun y‖) := by
  have hp := realified_linear_coordinate_norm b c φ hφ x
  have hs := realified_linear_coordinate_norm c b S hS (φ.baseChange ℝ x - y)
  have ht := norm_sub_le ((c.baseChange ℝ).equivFun (φ.baseChange ℝ x))
    ((c.baseChange ℝ).equivFun y)
  have hc := norm_sub_le ((b.baseChange ℝ).equivFun x)
    ((b.baseChange ℝ).equivFun (S.baseChange ℝ (φ.baseChange ℝ x - y)))
  rw [← map_sub] at ht hc
  have hdiff := ht.trans (add_le_add hp (le_refl ‖(c.baseChange ℝ).equivFun y‖))
  have hcorrect := hs.trans (mul_le_mul_of_nonneg_left hdiff
    (by positivity : 0 ≤ ((Fintype.card κ : ℝ) + 1) * (K + 1)))
  exact hc.trans (add_le_add (le_refl ‖(b.baseChange ℝ).equivFun x‖) hcorrect)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

theorem exists_bracketLiftMatrix_leftInverse [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    {H : ℕ} (hH : 1 ≤ H) (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H) :
    ∃ Q : Matrix κ μ ℚ, Q * bracketLiftMatrix b e = 1 ∧
      ∀ i j, RationalHeightLE (Q i j) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let f : E →ₗ[ℚ] (μ → ℚ) := b.equivFun.toLinearMap.comp E.subtype
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (b.equivFun.injective h)
  have hli : LinearIndependent ℚ (bracketLiftMatrix b e).col :=
    e.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  exact exists_bounded_rational_left_inverse (bracketLiftMatrix b e) hli hH he

noncomputable def realSubspaceCoordinateMap (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (κ → ℝ) :=
  (Matrix.mulVecLin (fun i j => (Q i j : ℝ))).comp (b.baseChange ℝ).equivFun.toLinearMap

omit [Fintype κ] in
@[simp] theorem realSubspaceCoordinateMap_apply (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (x : ℝ ⊗[ℚ] L) :
    realSubspaceCoordinateMap b Q x =
      (fun i j => (Q i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x := rfl

theorem realSubspaceCoordinateMap_lift [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1) (x : κ → ℝ) :
    realSubspaceCoordinateMap b Q (bracketSystemLift e x) = x := by
  classical
  rw [realSubspaceCoordinateMap_apply, bracketSystemLift_coordinates]
  change Q.map (Rat.castHom ℝ) *ᵥ ((bracketLiftMatrix b e).map (Rat.castHom ℝ) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, real_matrix_right_inverse Q (bracketLiftMatrix b e) hQ,
    Matrix.one_mulVec]

theorem lift_realSubspaceCoordinateMap [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ E.baseChange ℝ) :
    bracketSystemLift e (realSubspaceCoordinateMap b Q x) = x := by
  obtain ⟨v, rfl⟩ := exists_subspace_basis_coordinates e x hx
  rw [realSubspaceCoordinateMap_lift b e Q hQ]

theorem realSubspaceCoordinateMap_norm (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    {H : ℕ} (hQ : ∀ i j, RationalHeightLE (Q i j) H) (x : ℝ ⊗[ℚ] L) :
    ‖realSubspaceCoordinateMap b Q x‖ ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realSubspaceCoordinateMap_apply]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hQ i j).abs_real_le) _

theorem realSubspaceCoordinateMap_grid (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realSubspaceCoordinateMap b Q x ∈ realDenominatorGrid (matrixDenominator Q * l) := by
  rw [realSubspaceCoordinateMap_apply]
  exact real_matrix_denominator_grid Q l _ hx

end Erdos3

end

end OAI
