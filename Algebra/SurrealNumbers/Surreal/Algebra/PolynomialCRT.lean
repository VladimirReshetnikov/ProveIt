import Surreal.Algebra.PolynomialInterpolation

/-!
# Polynomial Chinese remainders and local idempotents

This file formalizes the quotient isomorphism `polynomial:eq:finiteCRT`
and its coordinate idempotents from `polynomial:thm:crt` in
`docs/surcomplex/polynomial-algebra/article.tex`. It combines Mathlib's
ideal Chinese remainder theorem with polynomial Taylor translation.

The ring isomorphism works in every characteristic. Characteristic zero
is needed only to express the Taylor coefficients as ordinary formal
derivatives divided by factorials. Empty index types and zero
multiplicities are allowed; a zero multiplicity contributes a zero ring.
-/

namespace Surreal
namespace FinitePolynomial

open Polynomial

noncomputable section

variable {K ι : Type*} [Field K]

/-- The local modulus at a node. -/
def nodeIdeal (a : K) (m : ℕ) : Ideal K[X] :=
  Ideal.span ({(X - C a) ^ m} : Set K[X])

/-- The ideal cutting off Taylor terms of degree at least `m`. -/
def jetIdeal (K : Type*) [Field K] (m : ℕ) : Ideal K[X] :=
  Ideal.span ({X ^ m} : Set K[X])

/-- Translation by a node identifies its local quotient with a truncated
polynomial ring at zero. -/
def localTaylorEquiv (a : K) (m : ℕ) :
    (K[X] ⧸ nodeIdeal a m) ≃+* (K[X] ⧸ jetIdeal K m) :=
  Ideal.quotientEquiv (nodeIdeal a m) (jetIdeal K m) (taylorEquiv a).toRingEquiv (by
    simp [nodeIdeal, jetIdeal, Ideal.map_span, taylorEquiv, taylorAlgHom,
      Polynomial.taylor_apply])

/-- The local quotient isomorphism acts by Taylor translation on
polynomial representatives. -/
theorem localTaylorEquiv_mk (a : K) (m : ℕ) (p : K[X]) :
    localTaylorEquiv a m (Ideal.Quotient.mk (nodeIdeal a m) p) =
      Ideal.Quotient.mk (jetIdeal K m) (taylor a p) := rfl

variable [Fintype ι]

local instance polynomialCRTDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The ideal of the product of the local moduli. -/
def interpolationIdeal (a : ι → K) (m : ι → ℕ) : Ideal K[X] :=
  Ideal.span ({interpolationModulus a m} : Set K[X])

omit [Fintype ι] in
/-- The pairwise coprime local node ideals used in the finite CRT. -/
theorem nodeIdeals_pairwise_coprime (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) : Pairwise fun i j => IsCoprime (nodeIdeal (a i) (m i))
      (nodeIdeal (a j) (m j)) := by
  intro i j hij
  exact (Ideal.isCoprime_span_singleton_iff _ _).mpr
    (interpolationModuli_pairwise_coprime a ha m hij)

/-- The ideal of the product is the intersection of the node ideals. -/
theorem interpolationIdeal_eq_iInf (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) : interpolationIdeal a m = ⨅ i, nodeIdeal (a i) (m i) :=
  (Ideal.iInf_span_singleton (interpolationModuli_pairwise_coprime a ha m)).symm

/-- The finite polynomial CRT of `polynomial:eq:finiteCRT`, with the
forward map given by the Taylor expansion at each node. -/
def polynomialCRT (a : ι → K) (ha : Function.Injective a) (m : ι → ℕ) :
    (K[X] ⧸ interpolationIdeal a m) ≃+* ((i : ι) → K[X] ⧸ jetIdeal K (m i)) :=
  ((Ideal.quotEquivOfEq (interpolationIdeal_eq_iInf a ha m)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => nodeIdeal (a i) (m i))
      (nodeIdeals_pairwise_coprime a ha m))).trans
        (RingEquiv.piCongrRight fun i => localTaylorEquiv (a i) (m i))

/-- The displayed forward map in `polynomial:eq:finiteCRT`. -/
theorem polynomialCRT_mk (a : ι → K) (ha : Function.Injective a) (m : ι → ℕ)
    (p : K[X]) (i : ι) :
    polynomialCRT a ha m (Ideal.Quotient.mk (interpolationIdeal a m) p) i =
      Ideal.Quotient.mk (jetIdeal K (m i)) (taylor (a i) p) := rfl

/-- Terms at or above the jet order vanish in the truncated polynomial
quotient, so a full Taylor polynomial and its finite jet have the same class. -/
theorem mk_taylor_eq_mk_truncated (a : K) (p : K[X]) (m : ℕ) :
    Ideal.Quotient.mk (jetIdeal K m) (taylor a p) =
      Ideal.Quotient.mk (jetIdeal K m)
        (∑ j ∈ Finset.range m, monomial j ((taylor a p).coeff j)) := by
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  simp [coeff_monomial, hj]

/-- The exact derivative-jet formula displayed in
`polynomial:eq:finiteCRT`. Characteristic zero makes every factorial
denominator invertible. -/
theorem polynomialCRT_mk_derivative_jet [CharZero K] (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (p : K[X]) (i : ι) :
    polynomialCRT a ha m (Ideal.Quotient.mk (interpolationIdeal a m) p) i =
      Ideal.Quotient.mk (jetIdeal K (m i))
        (∑ j ∈ Finset.range (m i),
          C ((derivative^[j] p).eval (a i) / (j.factorial : K)) * X ^ j) := by
  rw [polynomialCRT_mk, mk_taylor_eq_mk_truncated]
  simp only [taylor_coeff_eq_derivative, C_mul_X_pow_eq_monomial]

/-- The class that is the identity of factor `i` and zero in every other
factor of `polynomial:eq:finiteCRT`. -/
def crtIdempotent (a : ι → K) (ha : Function.Injective a) (m : ι → ℕ)
    (i : ι) : K[X] ⧸ interpolationIdeal a m := by
  classical
  exact (polynomialCRT a ha m).symm (fun j => if j = i then 1 else 0)

/-- Coordinate formula for the local identity classes. -/
theorem polynomialCRT_crtIdempotent (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (i j : ι) :
    polynomialCRT a ha m (crtIdempotent a ha m i) j =
      if j = i then 1 else 0 := by
  classical
  simp [crtIdempotent]

/-- A polynomial that is one modulo the selected local modulus and zero
modulo every other local modulus represents the corresponding coordinate
idempotent. In particular, this identifies any Bézout construction of the
classes `Eᵢ` in `polynomial:thm:crt` with the coordinate construction. -/
theorem mk_eq_crtIdempotent_of_local_congruences (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (i : ι) (p : K[X])
    (hp : ∀ j, (X - C (a j)) ^ m j ∣ p - if j = i then 1 else 0) :
    Ideal.Quotient.mk (interpolationIdeal a m) p = crtIdempotent a ha m i := by
  classical
  apply (polynomialCRT a ha m).injective
  ext j
  rw [polynomialCRT_mk, polynomialCRT_crtIdempotent]
  have hlocal : Ideal.Quotient.mk (nodeIdeal (a j) (m j)) p =
      Ideal.Quotient.mk (nodeIdeal (a j) (m j)) (if j = i then 1 else 0) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hp j))
  have h := congrArg (localTaylorEquiv (a j) (m j)) hlocal
  rw [localTaylorEquiv_mk, localTaylorEquiv_mk] at h
  by_cases hji : j = i <;> simpa [hji] using h

/-- Each coordinate idempotent has a polynomial representative of degree
below the product modulus, with the local congruences from the proof of
`polynomial:thm:crt`. -/
theorem exists_crtIdempotent_representative (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (i : ι) :
    ∃ p : K[X], p.degree < (∑ j, m j : ℕ) ∧
      (∀ j, (X - C (a j)) ^ m j ∣ p - if j = i then 1 else 0) ∧
      Ideal.Quotient.mk (interpolationIdeal a m) p = crtIdempotent a ha m i := by
  classical
  obtain ⟨p, hp, _⟩ := exists_unique_interpolation_representative a ha m
    (fun j => if j = i then 1 else 0)
  exact ⟨p, hp.1, hp.2, mk_eq_crtIdempotent_of_local_congruences a ha m i p hp.2⟩

/-- Each local identity class is idempotent (`polynomial:thm:crt`). -/
theorem crtIdempotent_mul_self (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (i : ι) :
    crtIdempotent a ha m i * crtIdempotent a ha m i = crtIdempotent a ha m i := by
  classical
  apply (polynomialCRT a ha m).injective
  ext j
  simp only [map_mul, Pi.mul_apply, polynomialCRT_crtIdempotent]
  split_ifs <;> simp

/-- Distinct local identity classes are orthogonal (`polynomial:thm:crt`). -/
theorem crtIdempotent_mul_of_ne (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) {i j : ι} (hij : i ≠ j) :
    crtIdempotent a ha m i * crtIdempotent a ha m j = 0 := by
  classical
  apply (polynomialCRT a ha m).injective
  ext k
  simp only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply,
    polynomialCRT_crtIdempotent]
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- The local identity classes sum to the identity, including the empty
product case where the quotient is the zero ring (`polynomial:thm:crt`). -/
theorem sum_crtIdempotent (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) : ∑ i, crtIdempotent a ha m i = 1 := by
  classical
  apply (polynomialCRT a ha m).injective
  ext j
  simp [polynomialCRT_crtIdempotent]

end

end FinitePolynomial
end Surreal
