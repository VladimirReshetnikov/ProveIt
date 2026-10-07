/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Adapt import paths to Mathlib v4.32.0 and simplify zero polynomial
coefficients explicitly. Mathematical statements unchanged. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import OAI.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
import OAI.Combinatorics.Progressions.Linear.RationalMatrixSeparation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def eval₂ (x : σ → S) : VectorPolynomial σ R V →ₗ[R] V :=
  TensorProduct.lift ((Algebra.lsmul R R V).toLinearMap.comp (MvPolynomial.aeval x).toLinearMap)

@[simp] theorem eval₂_tmul (x : σ → S) (p : MvPolynomial σ R) (v : V) :
    eval₂ x (p ⊗ₜ[R] v) = MvPolynomial.aeval x p • v := rfl

@[simp] theorem eval₂_monomial (x : σ → S) (α : σ →₀ ℕ) (v : V) :
    eval₂ x (monomial (R := R) α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.aeval_monomial]

theorem eval₂_algebraMap (x : σ → R) (p : VectorPolynomial σ R V) :
    eval₂ (fun i => algebraMap R S (x i)) p = eval x p := by
  have heval (q : MvPolynomial σ R) :
      MvPolynomial.aeval (fun i => algebraMap R S (x i)) q =
        algebraMap R S (MvPolynomial.aeval x q) := by
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  induction p using TensorProduct.inductionOn with
  | tmul q v => simp only [eval₂_tmul, eval_tmul, heval, IsScalarTower.algebraMap_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coordinate_eval₂ (f : V →ₗ[S] S) (x : σ → S) (p : VectorPolynomial σ R V) :
    f (eval₂ x p) = MvPolynomial.eval x (coordinate f.toAddMonoidHom p) := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, coordinate_sum, coordinate_monomial,
    eval₂_monomial, MvPolynomial.eval_monomial, map_smul, smul_eq_mul, mul_comm]
  rfl

theorem eval₂_ofCoordinates {ι : Type*} [Fintype ι] (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (x : σ → S) :
    eval₂ x (ofCoordinates (R := R) e p) =
      e.equivFun.symm (fun i => MvPolynomial.eval x (p i)) := by
  apply e.equivFun.injective
  funext i
  rw [e.equivFun.apply_symm_apply]
  change e.coord i (eval₂ x (ofCoordinates (R := R) e p)) = _
  rw [coordinate_eval₂]
  exact congrArg (MvPolynomial.eval x) (coordinate_ofCoordinates e p i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def integerRowLinear {J : Type*} [Fintype J] (a : J → ℤ) :
    (J → ℝ) →ₗ[ℝ] ℝ := ∑ j, (a j : ℝ) • LinearMap.proj j

theorem integerRowLinear_apply {J : Type*} [Fintype J] (a : J → ℤ) (w : J → ℝ) :
    integerRowLinear a w = ∑ j, (a j : ℝ) * w j := by
  simp [integerRowLinear]

noncomputable def integerRowPolynomial {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) : MvPolynomial I ℝ :=
  coordinate (integerRowLinear a).toAddMonoidHom p

theorem integerRowPolynomial_coeff {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (α : I →₀ ℕ) :
    (integerRowPolynomial a p).coeff α = ∑ j, (a j : ℝ) * coefficients p α j := by
  simp only [integerRowPolynomial, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    integerRowLinear_apply]

theorem integerRowPolynomial_eval {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial a p) = ∑ j, (a j : ℝ) * eval w p j := by
  have he : eval₂ w p = eval w p := by
    simpa using (eval₂_algebraMap (S := ℝ) w p)
  rw [integerRowPolynomial, ← coordinate_eval₂, he, integerRowLinear_apply]

theorem integerRowPolynomial_homogeneous {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) {h : ℕ} (hp : Homogeneous h p) :
    (integerRowPolynomial a p).IsHomogeneous h := by
  intro α hα
  by_contra hn
  have hd : α.degree ≠ h := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hn
  apply hα
  simp only [integerRowPolynomial_coeff, hp α hd, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero]

theorem integerRowPolynomial_nat_mul {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (t : ℕ) :
    integerRowPolynomial (fun j => (t : ℤ) * a j) p =
      MvPolynomial.C (t : ℝ) * integerRowPolynomial a p := by
  ext α
  rw [MvPolynomial.coeff_C_mul]
  simp only [integerRowPolynomial_coeff, Int.cast_mul, Int.cast_natCast, Finset.mul_sum, mul_assoc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

variable {X D E : Type*}

noncomputable def integralBasisPolynomialCoordinates
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U) : E → MvPolynomial X ℝ :=
  fun e => coordinate (b.coord e).toAddMonoidHom (restrictCoefficients U p hmem)

theorem integralBasisPolynomialCoordinates_weightedDegree
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U)
    {w : X → ℕ} {d : ℕ} (hp : DegreeLE w d p) (e : E) :
    (integralBasisPolynomialCoordinates U b p hmem e).weightedTotalDegree w ≤ d := by
  apply (scalar_weightedDegree_le_iff w d _).mpr
  intro α hα
  change (b.coord e) (coefficients (restrictCoefficients U p hmem) α) = 0
  have hz : coefficients (restrictCoefficients U p hmem) α = 0 := by
    apply Subtype.ext
    exact (coefficients_restrictCoefficients U p hmem α).trans (hp α hα)
  rw [hz, map_zero]

theorem integralBasisPolynomialCoordinates_totalDegree
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U)
    {d : ℕ} (hp : DegreeLE (1 : X → ℕ) d p) (e : E) :
    (integralBasisPolynomialCoordinates U b p hmem e).totalDegree ≤ d := by
  simpa only [MvPolynomial.weightedTotalDegree_one] using
    integralBasisPolynomialCoordinates_weightedDegree U b p hmem hp e

theorem eval_integralBasisPolynomialCoordinates [Fintype E]
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (M : D → E → ℤ) (hb : ∀ i e, (b e).val i = (M i e : ℝ))
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U) (x : X → ℝ) (i : D) :
    eval x p i = ∑ e, (M i e : ℝ) *
      MvPolynomial.eval x (integralBasisPolynomialCoordinates U b p hmem e) := by
  classical
  let q := restrictCoefficients U p hmem
  have heval : eval₂ x q = eval x q := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (eval₂_algebraMap (S := ℝ) x q)
  have hcoord (e : E) : (b.repr (eval x q)) e =
      MvPolynomial.eval x (integralBasisPolynomialCoordinates U b p hmem e) := by
    change (b.coord e) (eval x q) = _
    rw [← heval]
    exact coordinate_eval₂ (b.coord e) x q
  have hsum := congrArg (fun v : U => v.val i) (b.sum_repr (eval x q))
  have hpval : (eval x q).val i = eval x p i :=
    congrArg (fun v : D → ℝ => v i) (eval_restrictCoefficients U p hmem x)
  rw [hpval] at hsum
  rw [← hsum]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, hb, hcoord, mul_comm]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def linearPolynomial : (σ → V) →ₗ[R] VectorPolynomial σ R V where
  toFun a := ∑ i, monomial (Finsupp.single i 1) (a i)
  map_add' a b := by
    simp only [Pi.add_apply, monomial, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, monomial, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem linearPolynomial_apply (a : σ → V) :
    linearPolynomial (R := R) a = ∑ i, monomial (Finsupp.single i 1) (a i) := rfl

theorem coefficients_linearPolynomial_single (a : σ → V) (i : σ) :
    coefficients (linearPolynomial (R := R) a) (Finsupp.single i 1) = a i := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro j _ hji
    rw [coefficients_monomial, Finsupp.single_eq_of_ne]
    exact fun h => hji ((Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)) h.symm)
  · simp

theorem coefficients_linearPolynomial_of_ne (a : σ → V) (α : σ →₀ ℕ)
    (hα : ∀ i, Finsupp.single i 1 ≠ α) : coefficients (linearPolynomial (R := R) a) α = 0 := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm (hα i))]

@[simp] theorem coefficients_linearPolynomial_zero (a : σ → V) :
    coefficients (linearPolynomial (R := R) a) 0 = 0 := by
  apply coefficients_linearPolynomial_of_ne
  intro i h
  have hi := congrArg (fun α : σ →₀ ℕ => α i) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply, Nat.one_ne_zero] at hi

theorem eval₂_linearPolynomial {S : Type*} [CommRing S] [Algebra R S]
    [Module S V] [IsScalarTower R S V] (a : σ → V) (t : σ → S) :
    eval₂ t (linearPolynomial (R := R) a) = ∑ i, t i • a i := by
  simp [linearPolynomial_apply, eval₂_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R S V : Type*} [Finite σ] [CommRing R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eq_zero_of_eval₂_eq_zero_on_grid
    (length : σ → ℕ) (x : ∀ i, Fin (length i) → S)
    (hinj : ∀ i, Function.Injective (x i))
    {d : ℕ} {p : VectorPolynomial σ R V}
    (hp : DegreeLE (fun _ => 1) d p) (hlen : ∀ i, d < length i)
    (heval : ∀ j : ∀ i, Fin (length i), eval₂ (fun i => x i (j i)) p = 0) :
    p = 0 := by
  classical
  let e := Module.Free.chooseBasis S V
  have hcoord (k : Module.Free.ChooseBasisIndex S V) :
      coordinate (e.coord k).toAddMonoidHom p = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _
      (fun i => Finset.univ.image (x i))
    · intro i
      rw [Finset.card_image_of_injective _ (hinj i), Finset.card_univ,
        Fintype.card_fin]
      exact lt_of_le_of_lt
        ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
          ((degreeLE_one_iff_basis_totalDegree e d p).mp hp k)) (hlen i)
    · intro y hy
      have hy' : ∀ i, ∃ j, x i j = y i := by
        intro i
        simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hy i
      choose j hj using hy'
      have hx : (fun i => x i (j i)) = y := funext hj
      rw [← hx, ← coordinate_eval₂, heval, map_zero]
  apply coefficients.injective
  ext α
  simp only [map_zero, Finsupp.zero_apply]
  apply e.repr.injective
  ext k
  have hk := congrArg (fun polynomial : MvPolynomial σ S => polynomial.coeff α) (hcoord k)
  simpa only [coeff_coordinate, MvPolynomial.coeff_zero, map_zero,
    Finsupp.zero_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply] using hk

theorem eq_of_eval₂_eq_on_grid
    (length : σ → ℕ) (x : ∀ i, Fin (length i) → S)
    (hinj : ∀ i, Function.Injective (x i))
    {d : ℕ} {p q : VectorPolynomial σ R V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q)
    (hlen : ∀ i, d < length i)
    (heval : ∀ j : ∀ i, Fin (length i),
      eval₂ (fun i => x i (j i)) p = eval₂ (fun i => x i (j i)) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_eq_zero_on_grid length x hinj
  · intro α hα
    simp only [map_sub, Finsupp.sub_apply, hp α hα, hq α hα, sub_self]
  · exact hlen
  · intro j
    rw [map_sub, heval j, sub_self]

end Erdos3.VectorPolynomial

end

section

open scoped Matrix

namespace Erdos3

noncomputable def realMatrixPolynomialMap {ι κ σ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) :
    VectorPolynomial σ ℚ (κ → ℝ) →ₗ[ℚ] VectorPolynomial σ ℚ (ι → ℝ) :=
  VectorPolynomial.map ((Matrix.mulVecLin (fun i j => (A i j : ℝ))).restrictScalars ℚ)

@[simp] theorem coefficients_realMatrixPolynomialMap {ι κ σ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (v : VectorPolynomial σ ℚ (κ → ℝ)) (α : σ →₀ ℕ) :
    VectorPolynomial.coefficients (realMatrixPolynomialMap A v) α =
      (fun i j => (A i j : ℝ)) *ᵥ VectorPolynomial.coefficients v α := by
  rw [realMatrixPolynomialMap, VectorPolynomial.coefficients_map]
  rfl

theorem degreeLE_realMatrixPolynomialMap {ι κ σ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) {w : σ → ℕ} {d : ℕ} {v : VectorPolynomial σ ℚ (κ → ℝ)}
    (hv : VectorPolynomial.DegreeLE w d v) :
    VectorPolynomial.DegreeLE w d (realMatrixPolynomialMap A v) :=
  hv.map _

end Erdos3

end

section

namespace Erdos3

open scoped Matrix
open VectorPolynomial

variable {η κ σ : Type*} [Fintype κ] {ρ : η → Type*}

theorem real_jointMatrix_ker (A : ∀ i, Matrix (ρ i) κ ℚ) :
    LinearMap.ker (Matrix.mulVecLin (fun i j => (jointMatrix A i j : ℝ))) =
      ⨅ i, LinearMap.ker (Matrix.mulVecLin (fun j k => (A i j k : ℝ))) := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker,
    funext_iff, Pi.zero_apply]
  exact ⟨fun h i j => h ⟨i, j⟩, fun h ij => h ij.1 ij.2⟩

theorem realMatrixPolynomialMap_eq_zero_iff (A : Matrix η κ ℚ)
    (v : VectorPolynomial σ ℚ (κ → ℝ)) :
    realMatrixPolynomialMap A v = 0 ↔
      ∀ α, (fun i j => (A i j : ℝ)) *ᵥ coefficients v α = 0 := by
  constructor
  · intro h α
    have he := congrArg (fun q => coefficients q α) h
    simpa only [coefficients_realMatrixPolynomialMap, map_zero, Finsupp.zero_apply] using he
  · intro h
    apply coefficients.injective
    ext α i
    simpa only [coefficients_realMatrixPolynomialMap, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun (h α) i

theorem realMatrixPolynomialMap_joint_eq_zero_iff (A : ∀ i, Matrix (ρ i) κ ℚ)
    (v : VectorPolynomial σ ℚ (κ → ℝ)) :
    realMatrixPolynomialMap (jointMatrix A) v = 0 ↔
      ∀ i, realMatrixPolynomialMap (A i) v = 0 := by
  simp only [realMatrixPolynomialMap_eq_zero_iff]
  constructor
  · intro h i α
    funext j
    exact congrFun (h α) ⟨i, j⟩
  · intro h α
    funext ij
    exact congrFun (h ij.1 α) ij.2

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

theorem eval₂_mem_of_coefficients {σ R S V : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup V]
    [Module R V] [Module S V] [IsScalarTower R S V]
    (U : Submodule S V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ U) (x : σ → S) : eval₂ x p ∈ U := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval₂_monomial]
  exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end VectorPolynomial

open scoped Matrix
open VectorPolynomial

theorem realMatrixPolynomialMap_eval₂_eq_zero {ι κ σ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (v : VectorPolynomial σ ℚ (κ → ℝ))
    (hv : realMatrixPolynomialMap A v = 0) (x : σ → ℝ) :
    (fun i j => (A i j : ℝ)) *ᵥ eval₂ x v = 0 :=
  eval₂_mem_of_coefficients (LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ))))
    v ((realMatrixPolynomialMap_eq_zero_iff A v).mp hv) x

theorem eval₂_mem_real_joint_kernel {η κ σ : Type*} [Fintype κ] {ρ : η → Type*}
    (A : ∀ i, Matrix (ρ i) κ ℚ) (v : VectorPolynomial σ ℚ (κ → ℝ))
    (hv : realMatrixPolynomialMap (jointMatrix A) v = 0) (x : σ → ℝ) :
    eval₂ x v ∈ ⨅ i, LinearMap.ker (Matrix.mulVecLin (fun j k => (A i j k : ℝ))) := by
  simp only [Submodule.mem_iInf]
  intro i
  exact realMatrixPolynomialMap_eval₂_eq_zero (A i) v
    ((realMatrixPolynomialMap_joint_eq_zero_iff A v).mp hv i) x

end Erdos3

end

end OAI
