import FabiusFunction.FiniteMomentJacobi

/-!
# Naturality of the finite Gram--Stieltjes construction

The finite moment functional, its symmetric pairing, and the associated
Gram--Stieltjes and Jacobi data commute with scalar ring homomorphisms.  This
file packages those base-change facts in one leaf module, leaving the
foundational finite-moment files independent of downstream specializations.

The numerator statement is valid over commutative rings.  Normalization and
the Jacobi quotients use fields so that a ring homomorphism also preserves the
inverses occurring in their definitions.  All results are finite algebra;
there is no measure, positivity, or convergence hypothesis.
-/

set_option autoImplicit false

open Polynomial

namespace Fabius

noncomputable section

/-- Base change commutes with the moment pairing when both polynomial
arguments are mapped coefficientwise. -/
theorem momentPairing_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (moment : ℕ → R) (p q : R[X]) :
    momentPairing (fun n ↦ φ (moment n)) (p.map φ) (q.map φ) =
      φ (momentPairing moment p q) := by
  rw [momentPairing_apply, momentPairing_apply, ← Polynomial.map_mul,
    momentFunctional_map]

/-- Base change commutes with the fraction-free Gram--Stieltjes numerator. -/
theorem map_gramStieltjesNumerator {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (moment : ℕ → R) (n : ℕ) :
    (gramStieltjesNumerator moment n).map φ =
      gramStieltjesNumerator (fun k ↦ φ (moment k)) n := by
  ext k
  rw [Polynomial.coeff_map]
  by_cases hk : k < n + 1
  · rw [gramStieltjesNumerator_coeff moment n k hk,
      gramStieltjesNumerator_coeff (fun i ↦ φ (moment i)) n k hk]
    have hadj := RingHom.map_adjugate φ
      (momentHankelMatrix moment (n + 1))
    have hentry := congrArg
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) S ↦
        M ⟨k, hk⟩ (Fin.last n)) hadj
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply,
      momentHankelMatrix_map] using hentry
  · have hk' : n < k := by omega
    have hsource : (gramStieltjesNumerator moment n).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((gramStieltjesNumerator_natDegree_le moment n).trans_lt hk')
    have htarget :
        (gramStieltjesNumerator (fun i ↦ φ (moment i)) n).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((gramStieltjesNumerator_natDegree_le
          (fun i ↦ φ (moment i)) n).trans_lt hk')
    rw [hsource, htarget, map_zero]

/-- Base change commutes with the monic Gram--Stieltjes normalization. -/
theorem map_gramStieltjesPolynomial {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (moment : ℕ → K) (n : ℕ) :
    (gramStieltjesPolynomial moment n).map φ =
      gramStieltjesPolynomial (fun k ↦ φ (moment k)) n := by
  rw [gramStieltjesPolynomial, gramStieltjesPolynomial,
    Polynomial.map_mul, Polynomial.map_C, map_inv₀,
    map_momentHankelDet, map_gramStieltjesNumerator]

/-- Base change commutes with the finite Gram--Stieltjes norm quotient. -/
theorem map_gramStieltjesNorm {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (moment : ℕ → K) (n : ℕ) :
    φ (gramStieltjesNorm moment n) =
      gramStieltjesNorm (fun k ↦ φ (moment k)) n := by
  rw [gramStieltjesNorm, gramStieltjesNorm, map_div₀,
    map_momentHankelDet, map_momentHankelDet]

/-- Base change commutes with the diagonal finite Jacobi coefficient. -/
theorem map_gramStieltjesJacobiDiagonal
    {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (moment : ℕ → K) (n : ℕ) :
    φ (gramStieltjesJacobiDiagonal moment n) =
      gramStieltjesJacobiDiagonal (fun k ↦ φ (moment k)) n := by
  rw [gramStieltjesJacobiDiagonal, gramStieltjesJacobiDiagonal, map_div₀,
    map_gramStieltjesNorm]
  have hpair := momentPairing_map φ moment
    (Polynomial.X * gramStieltjesPolynomial moment n)
    (gramStieltjesPolynomial moment n)
  simp only [Polynomial.map_mul, Polynomial.map_X,
    map_gramStieltjesPolynomial] at hpair
  rw [hpair]

/-- Base change commutes with the subdiagonal finite Jacobi coefficient. -/
theorem map_gramStieltjesJacobiSubdiagonal
    {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (moment : ℕ → K) (n : ℕ) :
    φ (gramStieltjesJacobiSubdiagonal moment n) =
      gramStieltjesJacobiSubdiagonal (fun k ↦ φ (moment k)) n := by
  rw [gramStieltjesJacobiSubdiagonal,
    gramStieltjesJacobiSubdiagonal, map_div₀,
    map_gramStieltjesNorm, map_gramStieltjesNorm]

end

end Fabius
