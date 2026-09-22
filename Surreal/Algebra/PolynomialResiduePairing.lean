import Surreal.Algebra.PolynomialResidueDual
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Residue duality over a commutative coefficient ring

The residue pairing sends `h` to the functional `g ↦ λ(hg)` on the monic
polynomial quotient. Its inverse will be supplied by the explicit dual
polynomials, without a discriminant denominator.
-/

namespace Surreal.FinitePolynomial

open Polynomial Module

noncomputable section

section FiniteAlgebra

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

private theorem repr_eq_functional_mul (b : Basis ι R A) (l : A →ₗ[R] R)
    (d : ι → A) (hd : ∀ i j, l (b j * d i) = if j = i then 1 else 0)
    (h : A) (i : ι) : b.repr h i = l (h * d i) := by
  conv_rhs => rw [← b.sum_repr h]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hd, smul_eq_mul]
  simp

private theorem pairing_bijective (b : Basis ι R A) (l : A →ₗ[R] R)
    (d : ι → A) (hd : ∀ i j, l (b j * d i) = if j = i then 1 else 0) :
    Function.Bijective ((LinearMap.mul R A).compr₂ l) := by
  constructor
  · intro x y hxy
    apply b.repr.injective
    ext i
    rw [repr_eq_functional_mul b l d hd, repr_eq_functional_mul b l d hd]
    exact DFunLike.congr_fun hxy (d i)
  · intro f
    refine ⟨∑ i, f (b i) • d i, ?_⟩
    apply b.ext
    intro j
    change l ((∑ i, f (b i) • d i) * b j) = f (b j)
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
    simp_rw [mul_comm (d _) (b j), hd]
    simp

private theorem trace_eq_functional_dual_sum (b : Basis ι R A) (l : A →ₗ[R] R)
    (d : ι → A) (hd : ∀ i j, l (b j * d i) = if j = i then 1 else 0)
    (h : A) : Algebra.trace R A h = l ((∑ i, b i * d i) * h) := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  change (∑ i, Algebra.leftMulMatrix b h i i) = _
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, repr_eq_functional_mul b l d hd]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end FiniteAlgebra

variable {R : Type*} [CommRing R] (P : R[X]) (hP : P.Monic)

/-- The source's residue pairing, as a linear map to the linear dual.
It is defined over the coefficient ring itself, even with zero divisors. -/
def residuePairing : AdjoinRoot P →ₗ[R] Module.Dual R (AdjoinRoot P) :=
  (LinearMap.mul R (AdjoinRoot P)).compr₂ (residueFunctional P hP)

@[simp] theorem residuePairing_apply (h g : AdjoinRoot P) :
    residuePairing P hP h g = residueFunctional P hP (h * g) := rfl

private theorem residue_dual (i j : Fin P.natDegree) :
    residueFunctional P hP ((AdjoinRoot.powerBasisAux' hP) j *
      AdjoinRoot.mk P (dualPolynomial P i)) = if j = i then 1 else 0 := by
  have hb : (AdjoinRoot.powerBasisAux' hP) j = AdjoinRoot.root P ^ (j : ℕ) :=
    (AdjoinRoot.powerBasis' hP).basis_eq_pow j
  rw [hb]
  simpa only [eq_comm] using
    residueFunctional_root_pow_mul_dualPolynomial P hP i j

/-- The residue pairing is perfect over the original coefficient ring.
This proves the perfection clause of `polynomial:thm:residuepairing`,
including repeated roots and coefficient rings with zero divisors. -/
def residuePairingEquiv : AdjoinRoot P ≃ₗ[R] Module.Dual R (AdjoinRoot P) :=
  LinearEquiv.ofBijective (residuePairing P hP)
    (pairing_bijective (AdjoinRoot.powerBasisAux' hP) (residueFunctional P hP)
      (fun i => AdjoinRoot.mk P (dualPolynomial P i)) (residue_dual P hP))

@[simp] theorem residuePairingEquiv_apply (h g : AdjoinRoot P) :
    residuePairingEquiv P hP h g = residueFunctional P hP (h * g) := rfl

/-- The inverse pairing is a finite sum of the explicit dual elements.
This formula needs no division in the coefficient ring. -/
theorem residuePairingEquiv_symm_apply (f : Module.Dual R (AdjoinRoot P)) :
    (residuePairingEquiv P hP).symm f =
      ∑ i : Fin P.natDegree, f ((AdjoinRoot.powerBasisAux' hP) i) •
        AdjoinRoot.mk P (dualPolynomial P i) := by
  apply (residuePairingEquiv P hP).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (AdjoinRoot.powerBasisAux' hP).ext
  intro j
  rw [residuePairingEquiv_apply]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  simp_rw [mul_comm (AdjoinRoot.mk P _) ((AdjoinRoot.powerBasisAux' hP) j),
    residue_dual]
  simp

/-- The residue-dual vectors are an actual basis, obtained through the
perfect pairing from the coordinate dual of the power basis. -/
def residueDualBasis : Basis (Fin P.natDegree) R (AdjoinRoot P) :=
  (AdjoinRoot.powerBasisAux' hP).dualBasis.map (residuePairingEquiv P hP).symm

/-- This basis is the explicit polynomial family in
`polynomial:eq:dualbasis`. -/
theorem residueDualBasis_apply (i : Fin P.natDegree) :
    residueDualBasis P hP i = AdjoinRoot.mk P (dualPolynomial P i) := by
  rw [residueDualBasis, Basis.map_apply, residuePairingEquiv_symm_apply]
  simp only [Basis.dualBasis_apply_self]
  simp

/-- Coordinates of any quotient class are computed by pairing against
the explicit dual polynomials. -/
theorem quotient_repr_eq_residue (h : AdjoinRoot P) (i : Fin P.natDegree) :
    (AdjoinRoot.powerBasisAux' hP).repr h i =
      residueFunctional P hP (h * AdjoinRoot.mk P (dualPolynomial P i)) :=
  repr_eq_functional_mul _ _ _ (residue_dual P hP) h i

/-- The finite Euler identity in the quotient algebra. -/
theorem quotient_sum_basis_mul_dual :
    (∑ i : Fin P.natDegree, (AdjoinRoot.powerBasisAux' hP) i *
      AdjoinRoot.mk P (dualPolynomial P i)) = AdjoinRoot.mk P P.derivative := by
  have hb (i : Fin P.natDegree) : (AdjoinRoot.powerBasisAux' hP) i =
      AdjoinRoot.root P ^ (i : ℕ) := (AdjoinRoot.powerBasis' hP).basis_eq_pow i
  simp_rw [hb, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul]
  rw [← map_sum]
  apply congrArg (AdjoinRoot.mk P)
  exact (Fin.sum_univ_eq_sum_range (fun i => X ^ i * dualPolynomial P i) P.natDegree).trans
    (sum_X_pow_mul_dualPolynomial P)

/-- The universal trace identity `polynomial:eq:traceidentity`.
It holds over every commutative ring, including at collisions and in
positive characteristic, with no discriminant denominator. -/
theorem quotient_trace_eq_residue_derivative (h : AdjoinRoot P) :
    Algebra.trace R (AdjoinRoot P) h =
      residueFunctional P hP (AdjoinRoot.mk P P.derivative * h) := by
  rw [← quotient_sum_basis_mul_dual P hP]
  exact trace_eq_functional_dual_sum (AdjoinRoot.powerBasisAux' hP)
    (residueFunctional P hP) _ (residue_dual P hP) h

include hP in
/-- The trace identity on polynomial representatives is a single monic
division and top-coefficient extraction. -/
theorem quotient_trace_mk_eq_coeff (Q : R[X]) :
    Algebra.trace R (AdjoinRoot P) (AdjoinRoot.mk P Q) =
      ((P.derivative * Q) %ₘ P).coeff (P.natDegree - 1) := by
  rw [quotient_trace_eq_residue_derivative P hP, ← map_mul, residueFunctional_mk]

end

end Surreal.FinitePolynomial
