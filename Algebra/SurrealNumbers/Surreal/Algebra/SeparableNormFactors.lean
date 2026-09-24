import Surreal.Algebra.NormFormPolynomial
import Mathlib.RingTheory.Discriminant
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Separable norm forms as products of independent linear factors

The factorization and common-kernel prerequisites for `odg:thm:norm`.
Mathlib's nondegenerate trace form proves independence of the embedding
coordinates. Its product formula for the norm identifies the native norm
polynomial after coefficient extension, first on the infinite base-field
grid and then by multivariate polynomial extensionality.
-/

namespace Surreal.NormForm

open MvPolynomial Module

noncomputable section

variable {K L E ι : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
  [Module.Finite K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
  [Fintype ι] [DecidableEq ι]

/-- Rows are the ordinary field embeddings, columns are the chosen basis elements. -/
def embeddingMatrix (b : Basis ι K L) : Matrix (L →ₐ[K] E) ι E :=
  fun σ j => σ (b j)

/-- The embedding-coordinate map has zero common kernel. This is proved from the separable
trace pairing, not assumed as a rank condition. -/
theorem embeddingMatrix_injective (b : Basis ι K L) :
    Function.Injective (embeddingMatrix (E := E) b).mulVecLin := by
  have hu : IsUnit ((Algebra.traceMatrix K b).map (algebraMap K E)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit ((algebraMap K E).mapMatrix (Algebra.traceMatrix K b)).det
    rw [← RingHom.map_det]
    exact (Algebra.discr_isUnit_of_basis K b).map (algebraMap K E)
  rw [Algebra.traceMatrix_eq_embeddingsMatrix_mul_trans] at hu
  have hi := Matrix.mulVec_injective_of_isUnit hu
  intro x y h
  apply hi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact congrArg ((Algebra.embeddingsMatrix K E b).mulVec) h

/-- On every base-field coordinate tuple, the extended norm is the product of its embedding forms. -/
theorem eval_polynomial_embeddings (b : Basis ι K L) (x : ι → K) :
    algebraMap K E ((polynomial b).eval x) =
      ∏ σ : L →ₐ[K] E, ∑ j, σ (b j) * algebraMap K E (x j) := by
  rw [eval_polynomial, Algebra.norm_eq_prod_embeddings K E]
  apply Finset.prod_congr rfl
  intro σ _
  simp [Algebra.smul_def, mul_comm]

/-- The determinant norm polynomial itself factors into the embedding linear forms. -/
theorem polynomial_map_eq_prod [Infinite K] (b : Basis ι K L) :
    (polynomial b).map (algebraMap K E) =
      ∏ σ : L →ₐ[K] E, ∑ j, C (σ (b j)) * X j := by
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K E))
    (fun _ => Set.infinite_range_of_injective (algebraMap K E).injective)
  intro x hx
  have hx' : ∀ j, ∃ a : K, algebraMap K E a = x j := fun j => hx j (Set.mem_univ j)
  choose a ha using hx'
  have he : x = algebraMap K E ∘ a := funext (fun j => (ha j).symm)
  rw [he]
  rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
  rw [eval_polynomial_embeddings]
  simp only [map_prod, map_sum, map_mul, eval_C, eval_X, Function.comp_apply]

/-- The polynomial factorization specializes in any commutative target algebra. -/
theorem eval₂_polynomial_eq_prod [Infinite K] {B : Type*} [CommRing B]
    (b : Basis ι K L) (φ : E →+* B) (x : ι → B) :
    (polynomial b).eval₂ (φ.comp (algebraMap K E)) x =
      ∏ σ : L →ₐ[K] E, ∑ j, φ (σ (b j)) * x j := by
  rw [← MvPolynomial.eval₂_map, polynomial_map_eq_prod (E := E)]
  simp only [eval₂_prod, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X]

end
end Surreal.NormForm
