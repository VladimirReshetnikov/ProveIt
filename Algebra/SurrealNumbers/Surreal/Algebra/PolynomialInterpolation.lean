import Surreal.Algebra.PolynomialMultiplicity
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite Hermite interpolation

The existence and uniqueness clause of `polynomial:thm:crt` in
`docs/surcomplex/polynomial-algebra/article.tex` follows from Mathlib's
Chinese remainder theorem, the coprimality of distinct linear factors,
and polynomial division. The coefficient field has characteristic zero
when derivative jets are used.

Multiplicities may be zero, and the finite index type may be empty. The
degree bound uses `Polynomial.degree`, so the zero polynomial has degree
`⊥`; in particular, the unique interpolant for an empty collection of
conditions is the zero polynomial.
-/

namespace Surreal
namespace FinitePolynomial

open Polynomial

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The product of the local moduli in `polynomial:thm:crt`. -/
def interpolationModulus (a : ι → K) (m : ι → ℕ) : K[X] :=
  ∏ i, (X - C (a i)) ^ m i

/-- The interpolation modulus is monic even when all multiplicities vanish. -/
theorem interpolationModulus_monic (a : ι → K) (m : ι → ℕ) :
    (interpolationModulus a m).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C (a i)).pow (m i)

/-- The modulus degree is the total number of prescribed jet coordinates. -/
theorem interpolationModulus_degree (a : ι → K) (m : ι → ℕ) :
    (interpolationModulus a m).degree = (∑ i, m i : ℕ) := by
  simp [interpolationModulus, Polynomial.degree_prod, Polynomial.degree_pow,
    Polynomial.degree_X_sub_C]

omit [Fintype ι] in
/-- Distinct nodes give coprime local moduli, including zero powers. -/
theorem interpolationModuli_pairwise_coprime (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) : Pairwise fun i j =>
      IsCoprime ((X - C (a i)) ^ m i) ((X - C (a j)) ^ m j) := by
  intro i j hij
  exact (Polynomial.pairwise_coprime_X_sub_C ha hij).pow

/-- The product modulus divides a polynomial exactly when every local
modulus divides it, the kernel calculation in finite polynomial CRT. -/
theorem interpolationModulus_dvd_iff (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (p : K[X]) :
    interpolationModulus a m ∣ p ↔ ∀ i, (X - C (a i)) ^ m i ∣ p := by
  classical
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun j => (X - C (a j)) ^ m j)
      (Finset.mem_univ i)).trans h
  · intro h
    exact Fintype.prod_dvd_of_coprime (interpolationModuli_pairwise_coprime a ha m) h

/-- Every finite family of polynomial residue classes at distinct nodes
has a unique representative below the degree of the product modulus.
This is the finite CRT representative form of `polynomial:thm:crt`. -/
theorem exists_unique_interpolation_representative (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (q : ι → K[X]) :
    ∃! p : K[X], p.degree < (∑ i, m i : ℕ) ∧
      ∀ i, (X - C (a i)) ^ m i ∣ p - q i := by
  classical
  let I : ι → Ideal K[X] := fun i => Ideal.span ({(X - C (a i)) ^ m i} : Set K[X])
  have hI : Pairwise fun i j => IsCoprime (I i) (I j) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (interpolationModuli_pairwise_coprime a ha m hij)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hI q
  have hr' (i : ι) : (X - C (a i)) ^ m i ∣ r - q i :=
    Ideal.mem_span_singleton.mp (hr i)
  let P := interpolationModulus a m
  have hP : P ≠ 0 := (interpolationModulus_monic a m).ne_zero
  have hdeg : (r % P).degree < (∑ i, m i : ℕ) := by
    rw [← interpolationModulus_degree a m]
    exact Polynomial.degree_mod_lt r hP
  have hrem : P ∣ r % P - r := by
    refine ⟨-(r / P), ?_⟩
    rw [EuclideanDomain.mod_eq_sub_mul_div, sub_sub_cancel_left, mul_neg]
  have hlocal (i : ι) : (X - C (a i)) ^ m i ∣ r % P - q i := by
    have hi : (X - C (a i)) ^ m i ∣ r % P - r :=
      (Finset.dvd_prod_of_mem (fun j => (X - C (a j)) ^ m j)
        (Finset.mem_univ i)).trans hrem
    simpa only [sub_add_sub_cancel] using dvd_add hi (hr' i)
  refine ⟨r % P, ⟨hdeg, hlocal⟩, ?_⟩
  intro s hs
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt
  · apply (interpolationModulus_dvd_iff a ha m _).mpr
    intro i
    simpa only [sub_sub_sub_cancel_right] using dvd_sub (hs.2 i) (hlocal i)
  · rw [interpolationModulus_degree]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hs.1 hdeg)

section CharZero

variable [CharZero K]

/-- The finite Taylor polynomial that realizes one prescribed derivative
jet, expressed using Mathlib's polynomial translation. -/
def localJetPolynomial (a : K) (m : ℕ) (c : ℕ → K) : K[X] :=
  taylor (-a) (∑ j ∈ Finset.range m, monomial j (c j / (j.factorial : K)))

omit [CharZero K] in
/-- The coefficients of the translated local representative are precisely
the prescribed derivative values divided by their factorials. -/
theorem taylor_localJetPolynomial_coeff (a : K) (m : ℕ) (c : ℕ → K)
    {j : ℕ} (hj : j < m) :
    (taylor a (localJetPolynomial a m c)).coeff j = c j / (j.factorial : K) := by
  simp [localJetPolynomial, hj]

/-- A finite derivative jet at one point has a polynomial representative. -/
theorem localJetPolynomial_derivative (a : K) (m : ℕ) (c : ℕ → K)
    {j : ℕ} (hj : j < m) :
    (derivative^[j] (localJetPolynomial a m c)).eval a = c j := by
  have h := taylor_localJetPolynomial_coeff a m c hj
  rw [taylor_coeff_eq_derivative] at h
  exact (div_left_inj' (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))).mp h

/-- Finite Hermite interpolation, the existence and uniqueness clause of
`polynomial:thm:crt`: at finitely many distinct nodes, arbitrary derivative
jets are realized by a unique polynomial of degree below the total
multiplicity. Values of `c i j` with `m i ≤ j` are unused. -/
theorem exists_unique_hermite_interpolant (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (c : ι → ℕ → K) :
    ∃! p : K[X], p.degree < (∑ i, m i : ℕ) ∧
      ∀ i j, j < m i → (derivative^[j] p).eval (a i) = c i j := by
  obtain ⟨p, hp, huniq⟩ := exists_unique_interpolation_representative a ha m
    (fun i => localJetPolynomial (a i) (m i) (c i))
  refine ⟨p, ⟨hp.1, ?_⟩, ?_⟩
  · intro i j hj
    exact ((derivative_jets_eq_iff_dvd_sub p
      (localJetPolynomial (a i) (m i) (c i)) (a i) (m i)).mpr (hp.2 i) j hj).trans
        (localJetPolynomial_derivative (a i) (m i) (c i) hj)
  · intro q hq
    apply huniq q
    refine ⟨hq.1, fun i => ?_⟩
    apply (derivative_jets_eq_iff_dvd_sub q
      (localJetPolynomial (a i) (m i) (c i)) (a i) (m i)).mp
    intro j hj
    exact (hq.2 i j hj).trans
      (localJetPolynomial_derivative (a i) (m i) (c i) hj).symm

/-- Hermite interpolation with the derivative data indexed by precisely
the requested finite jets. Empty node sets and zero multiplicities remain
included. -/
theorem exists_unique_hermite_interpolant_fin (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (c : (i : ι) → Fin (m i) → K) :
    ∃! p : K[X], p.degree < (∑ i, m i : ℕ) ∧
      ∀ i (j : Fin (m i)), (derivative^[j.val] p).eval (a i) = c i j := by
  let d : ι → ℕ → K := fun i j => if hj : j < m i then c i ⟨j, hj⟩ else 0
  obtain ⟨p, hp, huniq⟩ := exists_unique_hermite_interpolant a ha m d
  refine ⟨p, ⟨hp.1, ?_⟩, ?_⟩
  · intro i j
    simpa only [d, dif_pos j.isLt] using hp.2 i j.val j.isLt
  · intro q hq
    apply huniq q
    refine ⟨hq.1, fun i j hj => ?_⟩
    simpa only [d, dif_pos hj] using hq.2 i ⟨j, hj⟩

end CharZero

end

end FinitePolynomial
end Surreal
