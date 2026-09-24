import Surreal.Algebra.PolynomialInverseJet

/-!
# The constructive finite Hermite formula

This file formalizes the interpolant construction in the proof of
`polynomial:thm:crt` in `docs/surcomplex/polynomial-algebra/article.tex`:
take the remainder modulo `P` of the finite sum `∑ᵢ Pᵢ Cᵢ qᵢ`.
The factors `Pᵢ Cᵢ` are the explicit inverse-jet representatives already
proved to have the required local congruences.

The formula realizes arbitrary polynomial residue representatives. In
characteristic zero, choosing the local Taylor representatives realizes
arbitrary derivative jets. The formulas include empty node sets and zero
multiplicities, and make no convergence assertion.
-/

namespace Surreal.FinitePolynomial

noncomputable section

open Polynomial

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The constructive CRT interpolant: the remainder of the explicit
inverse-jet weighted sum modulo the product of the local moduli. -/
def hermiteInterpolant (a : ι → K) (m : ι → ℕ) (q : ι → K[X]) : K[X] :=
  (∑ i, inverseJetIdempotentPolynomial a m i * q i) % interpolationModulus a m

/-- The degree bound in the constructive finite Hermite formula. -/
theorem hermiteInterpolant_degree_lt (a : ι → K) (m : ι → ℕ) (q : ι → K[X]) :
    (hermiteInterpolant a m q).degree < (∑ i, m i : ℕ) := by
  rw [hermiteInterpolant, ← interpolationModulus_degree a m]
  exact Polynomial.degree_mod_lt _ (interpolationModulus_monic a m).ne_zero

/-- Before taking the remainder, the explicit weighted sum already has
the prescribed class in every local quotient. -/
theorem inverseJet_sum_local_congruences (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (q : ι → K[X]) (j : ι) :
    (X - C (a j)) ^ m j ∣
      (∑ i, inverseJetIdempotentPolynomial a m i * q i) - q j := by
  classical
  let f := Ideal.Quotient.mk (nodeIdeal (a j) (m j))
  have hE (i : ι) : f (inverseJetIdempotentPolynomial a m i) =
      if j = i then 1 else 0 := by
    have h : f (inverseJetIdempotentPolynomial a m i) = f (if j = i then 1 else 0) :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
        (inverseJetIdempotentPolynomial_local_congruences a ha m i j))
    by_cases hji : j = i <;> simpa [hji] using h
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq.mp
  change f (∑ i, inverseJetIdempotentPolynomial a m i * q i) = f (q j)
  simp [hE]

/-- Taking the remainder preserves every local residue condition in the
constructive inverse to `polynomial:eq:finiteCRT`. -/
theorem hermiteInterpolant_local_congruences (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (q : ι → K[X]) (j : ι) :
    (X - C (a j)) ^ m j ∣ hermiteInterpolant a m q - q j := by
  let S := ∑ i, inverseJetIdempotentPolynomial a m i * q i
  have hrem : interpolationModulus a m ∣ hermiteInterpolant a m q - S := by
    refine ⟨-(S / interpolationModulus a m), ?_⟩
    change S % interpolationModulus a m - S = _
    rw [EuclideanDomain.mod_eq_sub_mul_div, sub_sub_cancel_left, mul_neg]
  have hlocal : (X - C (a j)) ^ m j ∣ hermiteInterpolant a m q - S :=
    (interpolationModulus_dvd_iff a ha m _).mp hrem j
  simpa only [S, sub_add_sub_cancel] using
    dvd_add hlocal (inverseJet_sum_local_congruences a ha m q j)

/-- The constructive formula is the unique representative below the
product modulus degree with its prescribed residue classes. -/
theorem hermiteInterpolant_unique (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (q : ι → K[X]) (p : K[X])
    (hp : p.degree < (∑ i, m i : ℕ))
    (hlocal : ∀ i, (X - C (a i)) ^ m i ∣ p - q i) :
    p = hermiteInterpolant a m q := by
  obtain ⟨r, _, huniq⟩ := exists_unique_interpolation_representative a ha m q
  exact (huniq p ⟨hp, hlocal⟩).trans
    (huniq _ ⟨hermiteInterpolant_degree_lt a m q,
      hermiteInterpolant_local_congruences a ha m q⟩).symm

/-- The explicit interpolant has the requested image under the quotient
isomorphism, so the formula is a constructive inverse on polynomial
representatives of the local factors. -/
theorem polynomialCRT_hermiteInterpolant (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (q : ι → K[X]) (i : ι) :
    polynomialCRT a ha m
        (Ideal.Quotient.mk (interpolationIdeal a m) (hermiteInterpolant a m q)) i =
      Ideal.Quotient.mk (jetIdeal K (m i)) (taylor (a i) (q i)) := by
  have hlocal : Ideal.Quotient.mk (nodeIdeal (a i) (m i)) (hermiteInterpolant a m q) =
      Ideal.Quotient.mk (nodeIdeal (a i) (m i)) (q i) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      (hermiteInterpolant_local_congruences a ha m q i))
  exact congrArg (localTaylorEquiv (a i) (m i)) hlocal

/-- The explicit inverse of `polynomial:eq:finiteCRT` on arbitrary
polynomial representatives in the local Taylor variables. Each local
polynomial is translated back before the finite interpolation formula. -/
theorem polynomialCRT_symm_mk (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (q : ι → K[X]) :
    (polynomialCRT a ha m).symm (fun i => Ideal.Quotient.mk (jetIdeal K (m i)) (q i)) =
      Ideal.Quotient.mk (interpolationIdeal a m)
        (hermiteInterpolant a m (fun i => taylor (-a i) (q i))) := by
  apply (polynomialCRT a ha m).injective
  ext i
  rw [RingEquiv.apply_symm_apply, polynomialCRT_hermiteInterpolant]
  simp [taylor_taylor]

/-- Specialization of the constructive formula to derivative jet data. -/
def hermiteJetInterpolant (a : ι → K) (m : ι → ℕ) (c : ι → ℕ → K) : K[X] :=
  hermiteInterpolant a m (fun i => localJetPolynomial (a i) (m i) (c i))

/-- The explicit derivative-jet interpolant has degree below the total
multiplicity. -/
theorem hermiteJetInterpolant_degree_lt (a : ι → K) (m : ι → ℕ) (c : ι → ℕ → K) :
    (hermiteJetInterpolant a m c).degree < (∑ i, m i : ℕ) :=
  hermiteInterpolant_degree_lt a m _

/-- The explicit finite sum from the proof of `polynomial:thm:crt`
realizes every prescribed derivative below the corresponding multiplicity. -/
theorem hermiteJetInterpolant_derivative [CharZero K] (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (c : ι → ℕ → K)
    (i : ι) {j : ℕ} (hj : j < m i) :
    (derivative^[j] (hermiteJetInterpolant a m c)).eval (a i) = c i j := by
  have h := (derivative_jets_eq_iff_dvd_sub (hermiteJetInterpolant a m c)
    (localJetPolynomial (a i) (m i) (c i)) (a i) (m i)).mpr
      (hermiteInterpolant_local_congruences a ha m _ i)
  exact (h j hj).trans (localJetPolynomial_derivative (a i) (m i) (c i) hj)

/-- The explicit derivative-jet formula is the unique polynomial of the
required degree with the requested derivatives. -/
theorem hermiteJetInterpolant_unique [CharZero K] (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (c : ι → ℕ → K) (p : K[X])
    (hp : p.degree < (∑ i, m i : ℕ))
    (hjet : ∀ i j, j < m i → (derivative^[j] p).eval (a i) = c i j) :
    p = hermiteJetInterpolant a m c := by
  apply hermiteInterpolant_unique a ha m _ p hp
  intro i
  apply (derivative_jets_eq_iff_dvd_sub p
    (localJetPolynomial (a i) (m i) (c i)) (a i) (m i)).mp
  intro j hj
  exact (hjet i j hj).trans (localJetPolynomial_derivative (a i) (m i) (c i) hj).symm

end

end Surreal.FinitePolynomial
