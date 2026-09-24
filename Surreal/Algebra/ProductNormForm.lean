import Surreal.Algebra.NormFormPolynomial
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Norm forms of finite products

The product-algebra prerequisite for `odg:dec:thm:etale`. The factors may
have different dimensions. All norm identities use Mathlib's native
algebra norm and work with arbitrary bases of the product algebra.
-/

namespace Surreal.NormForm

open Module MvPolynomial
open scoped Matrix

noncomputable section

/-- The determinant of a dependent block diagonal matrix is the product of its determinants. -/
theorem det_blockDiagonal_dep {R H : Type*} [CommRing R] [Fintype H]
    {ι : H → Type*} [∀ h, Fintype (ι h)] [DecidableEq H] [∀ h, DecidableEq (ι h)]
    (M : ∀ h, Matrix (ι h) (ι h) R) :
    (Matrix.blockDiagonal' M).det = ∏ h, (M h).det := by
  classical
  letI : LinearOrder H := LinearOrder.lift' (Fintype.equivFin H) (Fintype.equivFin H).injective
  rw [(Matrix.blockTriangular_blockDiagonal' M).det_fintype]
  apply Finset.prod_congr rfl
  intro h _
  let e : {i : (Σ h, ι h) // i.1 = h} ≃ ι h :=
    { toFun := fun i => i.2 ▸ i.1.2
      invFun := fun i => ⟨⟨h, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨h', i⟩, he⟩
        change h' = h at he
        subst h'
        rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_reindex_self e.symm]
  congr 1
  ext i j
  rcases i with ⟨⟨hi, i⟩, hei⟩
  rcases j with ⟨⟨hj, j⟩, hej⟩
  change hi = h at hei
  change hj = h at hej
  subst hi
  subst hj
  simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, e]

/-- Native multiplication in a product algebra is block diagonal in its product basis. -/
theorem leftMulMatrix_pi {R H : Type*} [CommRing R] [Fintype H] [DecidableEq H]
    {L : H → Type*} [∀ h, CommRing (L h)] [∀ h, Algebra R (L h)]
    {ι : H → Type*} [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    (b : ∀ h, Basis (ι h) R (L h)) (x : ∀ h, L h) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' (fun h => Algebra.leftMulMatrix (b h) (x h)) := by
  ext ⟨h, i⟩ ⟨k, j⟩
  by_cases he : h = k
  · subst k
    simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]
  · simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply,
      Matrix.blockDiagonal'_apply_ne, he]

/-- The algebra norm on a finite dependent product is the product of the component norms. -/
theorem algebra_norm_pi {R H : Type*} [CommRing R] [Fintype H] [DecidableEq H]
    {L : H → Type*} [∀ h, CommRing (L h)] [∀ h, Algebra R (L h)]
    {ι : H → Type*} [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    (b : ∀ h, Basis (ι h) R (L h)) (x : ∀ h, L h) :
    Algebra.norm R x = ∏ h, Algebra.norm R (x h) := by
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_blockDiagonal_dep]
  simp_rw [Algebra.norm_eq_matrix_det (b _)]

/-- Transporting a basis along an algebra equivalence preserves the native norm polynomial. -/
theorem polynomial_basis_map {K S T J : Type*} [Field K] [Infinite K]
    [CommRing S] [CommRing T] [Algebra K S] [Algebra K T] [Fintype J] [DecidableEq J]
    (b : Basis J K S) (e : S ≃ₐ[K] T) :
    polynomial (b.map e.toLinearEquiv) = polynomial b := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomial, eval_polynomial]
  have he : (∑ j, x j • (b.map e.toLinearEquiv) j) = e (∑ j, x j • b j) := by
    simp
  rw [he, Algebra.norm_eq_of_algEquiv]

section Coordinates

variable {K H J : Type*} [Field K] [Fintype H] [DecidableEq H]
  {L : H → Type*} [∀ h, CommRing (L h)] [∀ h, Algebra K (L h)]
  {ι : H → Type*} [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
  [Fintype J] [DecidableEq J]

/-- Coordinates of a product-basis vector in one component basis, after coefficient extension. -/
def componentCoordinates {B : Type*} [CommRing B] (b : Basis J K (∀ h, L h))
    (bs : ∀ h, Basis (ι h) K (L h)) (φ : K →+* B) (x : J → B) (h : H) (i : ι h) : B :=
  ∑ j, φ ((bs h).repr (b j h) i) * x j

/-- The component norm after substituting the coordinates of the chosen product basis. -/
def componentPolynomial (b : Basis J K (∀ h, L h))
    (bs : ∀ h, Basis (ι h) K (L h)) (h : H) : MvPolynomial J K :=
  (polynomial (bs h)).eval₂ C (fun i => ∑ j, C ((bs h).repr (b j h) i) * X j)

omit [Fintype H] [DecidableEq H] [DecidableEq J] in
/-- Substitution commutes with arbitrary scalar evaluation. -/
theorem eval₂_componentPolynomial {B : Type*} [CommRing B]
    (b : Basis J K (∀ h, L h)) (bs : ∀ h, Basis (ι h) K (L h))
    (φ : K →+* B) (x : J → B) (h : H) :
    (componentPolynomial b bs h).eval₂ φ x =
      (polynomial (bs h)).eval₂ φ (componentCoordinates b bs φ x h) := by
  change (eval₂Hom φ x) ((polynomial (bs h)).eval₂ C _) = _
  rw [eval₂_comp_left]
  simp only [Function.comp_def, coe_eval₂Hom, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X]
  congr 1
  ext a
  simp

omit [Fintype H] [DecidableEq H] [DecidableEq J] in
/-- On base-field coordinates the component factor is exactly the native component norm. -/
theorem eval_componentPolynomial (b : Basis J K (∀ h, L h))
    (bs : ∀ h, Basis (ι h) K (L h)) (x : J → K) (h : H) :
    (componentPolynomial b bs h).eval x = Algebra.norm K (∑ j, x j • b j h) := by
  change (componentPolynomial b bs h).eval₂ (RingHom.id K) x = _
  rw [eval₂_componentPolynomial, eval₂_id, eval_polynomial]
  congr 1
  have he (i : ι h) : componentCoordinates b bs (RingHom.id K) x h i =
      (bs h).repr (∑ j, x j • b j h) i := by
    simp [componentCoordinates, map_sum, map_smul, mul_comm]
  simp_rw [he]
  exact (bs h).sum_repr _

/-- The native norm polynomial factors by components, for every basis of the product algebra. -/
theorem polynomial_pi [Infinite K] (b : Basis J K (∀ h, L h))
    (bs : ∀ h, Basis (ι h) K (L h)) :
    polynomial b = ∏ h, componentPolynomial b bs h := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomial, algebra_norm_pi bs, map_prod]
  apply Finset.prod_congr rfl
  intro h _
  rw [eval_componentPolynomial]
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply]

omit [DecidableEq H] [∀ h, DecidableEq (ι h)] in
/-- All component coordinates together retain every coordinate of the original basis,
including after arbitrary extension to a commutative ring. -/
theorem componentCoordinates_injective {B : Type*} [CommRing B]
    (b : Basis J K (∀ h, L h)) (bs : ∀ h, Basis (ι h) K (L h)) (φ : K →+* B) :
    Function.Injective (fun x : J → B =>
      fun s : (Σ h, ι h) => componentCoordinates b bs φ x s.1 s.2) := by
  let M := ((Pi.basis bs).toMatrix b).map φ
  let N := (b.toMatrix (Pi.basis bs)).map φ
  have hNM : N * M = 1 := by
    dsimp [N, M]
    rw [← Matrix.map_mul, Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ φ.map_zero φ.map_one]
  intro x y h
  have he : M *ᵥ x = M *ᵥ y := by
    funext s
    exact congrFun h s
  have hh := congrArg (fun v => N *ᵥ v) he
  simpa only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using hh

end Coordinates

end
end Surreal.NormForm
