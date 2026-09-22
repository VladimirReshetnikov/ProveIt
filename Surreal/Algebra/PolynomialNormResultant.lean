import Surreal.Algebra.PolynomialQuotient
import Surreal.Algebra.PolynomialResultant
import Surreal.Algebra.PolynomialTraceGram
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# The quotient norm and polynomial resultant

The multiplication-determinant and discriminant assertions of
`polynomial:thm:trace` and `polynomial:eq:tracegram` in
`docs/surcomplex/polynomial-algebra/article.tex`, for monic polynomials over
an arbitrary commutative ring. Finite monic remainders provide coefficient
specialization; no reducedness or separability assumption is used.

The proof reuses Mathlib's universal-coefficient induction. Over a splitting
field, multiplicativity reduces the norm to constants and linear factors;
the characteristic polynomial computes each linear-factor norm even when
the quotient has nilpotents. Monic remainder matrices then descend along
injective and surjective coefficient maps. Derivative degree padding is
removed explicitly using monicity, so the discriminant identities include
positive characteristic and degree zero.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

private def remainderDet {R : Type*} [CommRing R] (P Q : R[X]) (n : ℕ) : R :=
  Matrix.det (fun i j : Fin n => ((Q * X ^ (j : ℕ)) %ₘ P).coeff i)

private theorem map_remainderDet {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P Q : R[X]) (hP : P.Monic) (n : ℕ) :
    f (remainderDet P Q n) = remainderDet (P.map f) (Q.map f) n := by
  rw [remainderDet, remainderDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f hP]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

private theorem norm_mk_X_sub_C {K : Type*} [Field K] (P : K[X]) (hP : P.Monic)
    (a : K) :
    Algebra.norm K (AdjoinRoot.mk P (X - C a)) = (-1) ^ P.natDegree * P.eval a := by
  let b := AdjoinRoot.powerBasis hP.ne_zero
  have hchar : (Algebra.leftMulMatrix b.basis (AdjoinRoot.root P)).charpoly = P := by
    exact (charpoly_leftMulMatrix b).trans (AdjoinRoot.minpoly_powerBasis_gen_of_monic hP)
  have hc : Algebra.leftMulMatrix b.basis (AdjoinRoot.mk P (C a)) =
      Matrix.scalar (Fin b.dim) a := by
    change Algebra.leftMulMatrix b.basis (algebraMap K (AdjoinRoot P) a) = _
    rw [AlgHom.commutes]
    rfl
  rw [Algebra.norm_eq_matrix_det b.basis, map_sub, map_sub, AdjoinRoot.mk_X, hc,
    ← neg_sub (Matrix.scalar (Fin b.dim) a), Matrix.det_neg,
    ← Matrix.eval_charpoly, hchar, Fintype.card_fin]
  rfl

private theorem norm_mk_eq_resultant_of_splits {K : Type*} [Field K]
    (P Q : K[X]) (hP : P.Monic) (hQ : Q.Splits) :
    Algebra.norm K (AdjoinRoot.mk P Q) = P.resultant Q := by
  have hc (c : K) : Algebra.norm K (AdjoinRoot.mk P (C c)) = c ^ P.natDegree := by
    change Algebra.norm K (algebraMap K (AdjoinRoot P) c) = _
    simpa only [Fintype.card_fin, AdjoinRoot.powerBasis'_dim] using
      Algebra.norm_algebraMap_of_basis (AdjoinRoot.powerBasis' hP).basis c
  conv_lhs => rw [hQ.eq_prod_roots]
  rw [map_mul, map_mul, hc, map_multiset_prod, map_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def, norm_mk_X_sub_C P hP]
  rw [Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, ← hQ.natDegree_eq_card_roots]
  rw [resultant_swap, resultant_eq_leadingCoeff_mul_prod_eval Q P hQ, ← pow_mul]
  ring

private theorem remainderDet_eq_resultant {R : Type*} [CommRing R] (Q : R[X]) :
    ∀ (P : R[X]), P.Monic → remainderDet P Q P.natDegree = P.resultant Q := by
  induction Q using Polynomial.induction_of_Splits_of_injective_of_surjective with
  | Splits K Q hQ =>
    intro P hP
    exact (quotient_norm_eq_det P hP Q).symm.trans
      (norm_mk_eq_resultant_of_splits P Q hP hQ)
  | injective R S f hf Q ih =>
    intro P hP
    apply hf
    rw [map_remainderDet f P Q hP, ← Polynomial.resultant_map_map]
    simpa only [natDegree_map_eq_of_injective hf] using ih (P.map f) (hP.map f)
  | surjective R S f hf Q ih =>
    intro P hP
    obtain ⟨P', hmapP, hdegP, hmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.map_surjective f hf P) hP
    obtain ⟨Q', hmapQ, hdegQ⟩ :=
      Polynomial.exists_degree_eq_of_mem_lifts (Polynomial.map_surjective f hf Q)
    have h := congrArg f (ih Q' P' hmonic)
    rw [map_remainderDet f P' Q' hmonic, ← Polynomial.resultant_map_map] at h
    change remainderDet (P'.map f) (Q'.map f) P'.natDegree =
      (P'.map f).resultant (Q'.map f) P'.natDegree Q'.natDegree at h
    rw [hmapP, hmapQ, hdegP, natDegree_eq_of_degree_eq hdegQ] at h
    exact h

/-- The universal multiplication-determinant identity in
`polynomial:thm:trace`. The norm is the determinant of multiplication on
the actual monic polynomial quotient, including when it has nilpotents.
The result also includes degree zero, with both sides equal to one. -/
theorem quotient_norm_eq_resultant {R : Type*} [CommRing R]
    (P Q : R[X]) (hP : P.Monic) :
    Algebra.norm R (AdjoinRoot.mk P Q) = P.resultant Q :=
  (quotient_norm_eq_det P hP Q).trans (remainderDet_eq_resultant Q P hP)

/-- The monic derivative resultant is the signed native discriminant over
every commutative ring. Monicity removes the right-degree padding factor,
so this includes degree drops of the derivative in positive characteristic. -/
theorem monic_resultant_derivative_eq_sign_mul_discr {R : Type*} [CommRing R]
    (P : R[X]) (hP : P.Monic) :
    P.resultant P.derivative =
      (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) * P.discr := by
  nontriviality R
  by_cases hn : P.natDegree = 0
  · have h1 := Polynomial.eq_one_of_monic_natDegree_zero hP hn
    rw [h1, ← C_1, Polynomial.discr_C]
    simp
  · have hpad := Polynomial.resultant_add_right_deg P P.derivative P.natDegree
      P.derivative.natDegree (P.natDegree - 1 - P.derivative.natDegree) le_rfl
    rw [Nat.add_sub_of_le (natDegree_derivative_le P), hP.coeff_natDegree, one_pow,
      one_mul] at hpad
    rw [← hpad, Polynomial.resultant_deriv
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hn)), hP.leadingCoeff, mul_one]

/-- The determinant clause of `polynomial:eq:tracegram`: the trace-pairing
matrix has exactly the native polynomial discriminant as its determinant.
This holds over the original coefficient ring, including at repeated roots. -/
theorem quotient_det_traceMatrix_eq_discr {R : Type*} [CommRing R]
    (P : R[X]) (hP : P.Monic) :
    (Algebra.traceMatrix R (AdjoinRoot.powerBasisAux' hP)).det = P.discr := by
  rw [quotient_det_traceMatrix_eq_sign_mul_norm, quotient_norm_eq_resultant P P.derivative hP,
    monic_resultant_derivative_eq_sign_mul_discr P hP, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul]
  simp

end

end Surreal.FinitePolynomial
