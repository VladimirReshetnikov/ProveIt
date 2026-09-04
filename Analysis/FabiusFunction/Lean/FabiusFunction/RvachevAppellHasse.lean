import FabiusFunction.GeometricLagrangeQBinomial
import FabiusFunction.LagrangeRvachevSynthesis
import FabiusFunction.NewtonInterpolation
import FabiusFunction.PolynomialQTaylor
import FabiusFunction.SymmetricFunctionOrthogonality
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Hasse formulas for Rvachev--Appell decoders

This module supplies the finite algebra behind the explicit geometric
decoder formulas in the interpolation frontier.  For an arbitrary Appell
coefficient sequence `b`, replacing `X ^ n` by `Appell.poly b n` is the
finite Hasse-derivative operator

`P \mapsto sum_r C (b r) * hasseDeriv r P`.

For the reciprocal centered-Rvachev moments, all odd coefficients vanish,
so only the even Hasse derivatives remain.  Taylor's coefficient theorem and
Vieta's formula then identify the Hasse derivatives of a product of linear
factors with elementary symmetric functions.  This gives the displayed
q-falling-power Appell formula without analytic or convergence hypotheses.

The final section applies the same identity to Mathlib's Lagrange basis.  It
computes each decoder entry as a nodal weight times a finite elementary-
symmetric sum, and evaluates the nodal weight on `c, cq, ..., cq^n` by the
existing geometric divided-difference product.  These identities are total:
distinctness, positivity, and a nonzero mesh are needed by reconstruction
theorems, but not by the explicit coefficient formulas themselves.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

noncomputable section

namespace Appell

variable {R : Type*} [CommSemiring R]

/-- The coefficientwise polynomial transform associated with an Appell
sequence.  It sends the monomial `X ^ n` to `Appell.poly b n` and extends
`R`-linearly to every polynomial. -/
noncomputable def polynomialTransform (b : ℕ → R) : R[X] →ₗ[R] R[X] :=
  Polynomial.lsum fun n ↦
    (LinearMap.mulRight R (Appell.poly b n)).comp
      (Polynomial.CAlgHom : R →ₐ[R] R[X]).toLinearMap

/-- Applying `Appell.polynomialTransform b` is the coefficientwise
replacement of each monomial by the corresponding Appell polynomial. -/
@[simp]
theorem polynomialTransform_apply (b : ℕ → R) (P : R[X]) :
    polynomialTransform b P =
      P.sum fun n a ↦ C a * Appell.poly b n := by
  rfl

/-- The Appell polynomial transform sends a scalar monomial to the matching
Appell polynomial with the same scalar coefficient. -/
@[simp]
theorem polynomialTransform_monomial (b : ℕ → R) (n : ℕ) (a : R) :
    polynomialTransform b (monomial n a) = C a * Appell.poly b n := by
  simp [polynomialTransform]

private theorem polynomialTransform_monomial_eq_sum_hasseDeriv
    (b : ℕ → R) (n : ℕ) (a : R) {N : ℕ} (hn : n < N) :
    polynomialTransform b (monomial n a) =
      ∑ r ∈ range N, C (b r) * hasseDeriv r (monomial n a) := by
  have hcore :
      polynomialTransform b (monomial n a) =
        ∑ r ∈ range (n + 1),
          C (b r) * hasseDeriv r (monomial n a) := by
    rw [polynomialTransform_monomial, Appell.poly, Finset.mul_sum,
      ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hreflect : n + 1 - 1 - r = n - r := by omega
    rw [hreflect, Nat.sub_sub_self hrn, hasseDeriv_monomial,
      ← C_mul_X_pow_eq_monomial]
    simp only [C_mul]
    rw [Nat.choose_symm hrn]
    ring
  rw [hcore]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hn) ?_
  intro r hrN hr
  have hnr : n < r := by
    simp only [Finset.mem_range] at hr
    omega
  rw [hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hnr,
    Nat.cast_zero, zero_mul, monomial_zero_right, mul_zero]

/-- **Generic Appell--Hasse identity with an arbitrary finite cutoff.**
If the cutoff lies strictly above the degree of `P`, coefficientwise Appell
replacement is the finite sum of its Hasse derivatives weighted by `b`.
The statement is valid over every commutative semiring. -/
theorem polynomialTransform_eq_sum_hasseDeriv_of_natDegree_lt
    (b : ℕ → R) (P : R[X]) {N : ℕ} (hP : P.natDegree < N) :
    polynomialTransform b P =
      ∑ r ∈ range N, C (b r) * hasseDeriv r P := by
  have hrepr : P = ∑ n ∈ P.support, monomial n (P.coeff n) :=
    P.as_sum_support
  calc
    polynomialTransform b P =
        ∑ n ∈ P.support,
          polynomialTransform b (monomial n (P.coeff n)) := by
      have hmap := congrArg
        (fun Q : R[X] ↦ polynomialTransform b Q) hrepr
      simpa only [map_sum] using hmap
    _ = ∑ n ∈ P.support, ∑ r ∈ range N,
          C (b r) * hasseDeriv r (monomial n (P.coeff n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact polynomialTransform_monomial_eq_sum_hasseDeriv b n
        (P.coeff n)
        ((Polynomial.le_natDegree_of_mem_supp n hn).trans_lt hP)
    _ = ∑ r ∈ range N, ∑ n ∈ P.support,
          C (b r) * hasseDeriv r (monomial n (P.coeff n)) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ range N, C (b r) * hasseDeriv r P := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← Finset.mul_sum, ← map_sum, ← hrepr]

/-- **Canonical finite Appell--Hasse identity.**  The natural-degree cutoff
contains exactly all Hasse derivatives which can be nonzero. -/
theorem polynomialTransform_eq_sum_hasseDeriv
    (b : ℕ → R) (P : R[X]) :
    polynomialTransform b P =
      ∑ r ∈ range (P.natDegree + 1),
        C (b r) * hasseDeriv r P := by
  exact polynomialTransform_eq_sum_hasseDeriv_of_natDegree_lt b P
    (Nat.lt_succ_self P.natDegree)

end Appell

/-! ## The even Rvachev specialization -/

/-- Every odd coefficient of the reciprocal centered-Rvachev moment
sequence vanishes.  This is the finite recursion counterpart of the fact
that the reciprocal of an even exponential generating series is even. -/
@[simp]
theorem rvachevReciprocalMomentRat_odd (n : ℕ) :
    rvachevReciprocalMomentRat (2 * n + 1) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [rvachevReciprocalMomentRat, Bell.reciprocal_succ
          rvachevRawMomentRat rvachevRawMomentRat_zero (2 * n)]
      apply neg_eq_zero.mpr
      apply Finset.sum_eq_zero
      intro k hk
      obtain ⟨j, hjk | hjk⟩ := Nat.even_or_odd' k
      · subst k
        have hj : j ≤ n := by
          have := Finset.mem_range.mp hk
          omega
        have hsub : 2 * n + 1 - 2 * j = 2 * (n - j) + 1 := by omega
        simp [hsub]
      · subst k
        have hj : j < n := by
          have := Finset.mem_range.mp hk
          omega
        have hodd :
            Bell.reciprocal rvachevRawMomentRat (2 * j + 1) = 0 := by
          change rvachevReciprocalMomentRat (2 * j + 1) = 0
          exact ih j hj
        rw [hodd, zero_mul, mul_zero]

/-- The existing Rvachev deconvolution linear map is exactly the generic
Appell polynomial transform for the cast reciprocal-moment sequence. -/
theorem rvachevDeconvolutionLinearMap_eq_appellPolynomialTransform :
    rvachevDeconvolutionLinearMap =
      Appell.polynomialTransform
        (fun r ↦ (rvachevReciprocalMomentRat r : ℝ)) := by
  apply LinearMap.ext
  intro P
  rw [rvachevDeconvolutionLinearMap_apply,
    Appell.polynomialTransform_apply]
  unfold rvachevDeconvolvedPolynomial
  rw [Polynomial.sum_def, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [rvachevAppellPolynomial_eq_poly_cast]

/-- **Even Rvachev--Hasse formula.**  Rvachev polynomial deconvolution is a
finite sum of the even Hasse derivatives, with reciprocal centered-moment
coefficients.  The cutoff is exact for every polynomial, including zero. -/
theorem rvachevDeconvolvedPolynomial_eq_sum_even_hasseDeriv (P : ℝ[X]) :
    rvachevDeconvolvedPolynomial P =
      ∑ r ∈ range (P.natDegree / 2 + 1),
        C (rvachevReciprocalMomentRat (2 * r) : ℝ) *
          hasseDeriv (2 * r) P := by
  let K := P.natDegree / 2 + 1
  calc
    rvachevDeconvolvedPolynomial P =
        Appell.polynomialTransform
          (fun r ↦ (rvachevReciprocalMomentRat r : ℝ)) P := by
      rw [← rvachevDeconvolutionLinearMap_eq_appellPolynomialTransform]
      exact rvachevDeconvolutionLinearMap_apply P
    _ = ∑ r ∈ range (2 * K),
          C (rvachevReciprocalMomentRat r : ℝ) * hasseDeriv r P := by
      exact Appell.polynomialTransform_eq_sum_hasseDeriv_of_natDegree_lt
        (fun r ↦ (rvachevReciprocalMomentRat r : ℝ)) P (by
          dsimp only [K]
          omega)
    _ = ∑ r ∈ range K,
          C (rvachevReciprocalMomentRat (2 * r) : ℝ) *
            hasseDeriv (2 * r) P := by
      rw [sum_range_two_mul]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [rvachevReciprocalMomentRat_odd]
      norm_num
    _ = _ := rfl

/-! ## Products of roots and q-falling powers -/

/-- A Hasse derivative of a finite product of linear root factors, evaluated
at `y`, is the complementary elementary symmetric function of the translated
roots.  Multiplicities are retained because the family is indexed. -/
theorem eval_hasseDeriv_prod_X_sub_C_eq_elementarySymmetricEval
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) (y : R) {r : ℕ} (hr : r ≤ Fintype.card ι) :
    (hasseDeriv r (∏ i : ι, (X - C (a i)))).eval y =
      elementarySymmetricEval (fun i ↦ y - a i)
        (Fintype.card ι - r) := by
  have htaylor :
      Polynomial.taylor y (∏ i : ι, (X - C (a i))) =
        ∏ i : ι, (X + C (y - a i)) := by
    change (Polynomial.taylorAlgHom y) (∏ i : ι, (X - C (a i))) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _hi
    change Polynomial.taylor y (X - C (a i)) = X + C (y - a i)
    rw [map_sub, Polynomial.taylor_X, Polynomial.taylor_C]
    rw [map_sub]
    ring
  rw [← Polynomial.taylor_coeff y, htaylor]
  rw [Finset.prod_X_add_C_coeff Finset.univ
    (fun i ↦ y - a i) (by simpa using hr)]
  rw [← Finset.esymm_map_val]
  rfl

/-- Rvachev deconvolution of a finite monic root product, evaluated at `y`,
is the finite even reciprocal-moment sum of complementary elementary
symmetric functions. -/
theorem eval_rvachevDeconvolvedPolynomial_prod_X_sub_C
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (y : ℝ) :
    (rvachevDeconvolvedPolynomial
      (∏ i : ι, (X - C (a i)))).eval y =
      ∑ r ∈ range (Fintype.card ι / 2 + 1),
        (rvachevReciprocalMomentRat (2 * r) : ℝ) *
          elementarySymmetricEval (fun i ↦ y - a i)
            (Fintype.card ι - 2 * r) := by
  rw [rvachevDeconvolvedPolynomial_eq_sum_even_hasseDeriv]
  have hdegree :
      (∏ i : ι, (X - C (a i))).natDegree = Fintype.card ι := by
    rw [natDegree_prod_of_monic _ _ fun i _hi ↦ monic_X_sub_C (a i)]
    simp
  rw [hdegree, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : 2 * r ≤ Fintype.card ι := by
    have := Finset.mem_range.mp hr
    omega
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    eval_hasseDeriv_prod_X_sub_C_eq_elementarySymmetricEval a y hrle]

/-- **Explicit q-falling Rvachev--Appell formula.**  Deconvolving
`product_{j<k} (X - q^j c)` and evaluating at `y` gives the even
reciprocal-moment sum of the elementary symmetric functions in
`y - c, y - qc, ..., y - q^(k-1)c`.  This is the algebraic formula in
`gq:prop:q-Appell-falling`; no assumptions on `c` or `q` are required. -/
theorem eval_rvachevDeconvolvedPolynomial_qFallingPower
    (c q y : ℝ) (k : ℕ) :
    (rvachevDeconvolvedPolynomial (qFallingPower c q k)).eval y =
      ∑ r ∈ range (k / 2 + 1),
        (rvachevReciprocalMomentRat (2 * r) : ℝ) *
          elementarySymmetricEval
            (fun j : Fin k ↦ y - q ^ (j : ℕ) * c) (k - 2 * r) := by
  rw [qFallingPower, ← Fin.prod_univ_eq_prod_range]
  simpa only [Fintype.card_fin] using
    (eval_rvachevDeconvolvedPolynomial_prod_X_sub_C
      (fun j : Fin k ↦ q ^ (j : ℕ) * c) y)

/-! ## Explicit finite Lagrange--Rvachev decoder columns -/

/-- A Mathlib Lagrange basis is its nodal weight times the monic product of
all root factors other than the selected node.  The subtype presentation
keeps repeated indexed nodes, rather than collapsing them to a set of
values. -/
theorem lagrangeBasis_eq_nodalWeight_mul_prod_X_sub_C
    {K ι : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (v : ι → K) {i : ι} (hi : i ∈ s) :
    Lagrange.basis s v i =
      C (Lagrange.nodalWeight s v i) *
        ∏ j : ↥(s.erase i), (X - C (v (j : ι))) := by
  calc
    Lagrange.basis s v i =
        C (Lagrange.nodalWeight s v i) * Lagrange.nodal (s.erase i) v := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
        ← Lagrange.nodal_erase_eq_nodal_div hi]
    _ = C (Lagrange.nodalWeight s v i) *
        ∏ j ∈ s.erase i, (X - C (v j)) := rfl
    _ = C (Lagrange.nodalWeight s v i) *
        ∏ j : ↥(s.erase i), (X - C (v (j : ι))) := by
      congr 1
      exact (Finset.prod_coe_sort
        (s.erase i) (fun j : ι ↦ X - C (v j))).symm

/-- **Elementary-symmetric formula for an arbitrary finite decoder
column.**  The sampled deconvolution of a Lagrange basis is its nodal weight
times the even Rvachev--Hasse sum over all translated unselected nodes.
Neither node distinctness nor `M ≠ 0` is needed for this totalized identity. -/
theorem lagrangeRvachevDecoder_eq_nodalWeight_mul_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {i : ι} (hi : i ∈ s) (M : ℕ) (k : ℤ) :
    lagrangeRvachevDecoder s v M k i =
      Lagrange.nodalWeight s v i *
        ∑ r ∈ range ((s.card - 1) / 2 + 1),
          (rvachevReciprocalMomentRat (2 * r) : ℝ) *
            elementarySymmetricEval
              (fun j : ↥(s.erase i) ↦
                (k : ℝ) / (M : ℝ) - v (j : ι))
              (s.card - 1 - 2 * r) := by
  rw [lagrangeRvachevDecoder,
    lagrangeBasis_eq_nodalWeight_mul_prod_X_sub_C s v hi,
    rvachevDeconvolvedPolynomial_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C,
    eval_rvachevDeconvolvedPolynomial_prod_X_sub_C]
  simp only [Fintype.card_coe, Finset.card_erase_of_mem hi]

/-- **Explicit geometric nodal prefactor.**  For the nodes
`c, cq, ..., cq^n`, the nodal weight at `cq^j` is

`(-1)^j / (c^n q^(choose(j,2)+j(n-j)) (q;q)_j (q;q)_(n-j))`.

The exponent is the nonnegative form of the manuscript exponent
`-nj + choose(j+1,2)`.  The identity is total even at zero or colliding
nodes; in those cases it describes Mathlib's inverse-defined basis, not an
interpolation cardinal. -/
theorem geometric_nodalWeight_eq_geometricQPochhammer
    {K : Type*} [Field K] (c q : K) (n j : ℕ) (hj : j ≤ n) :
    Lagrange.nodalWeight (range (n + 1))
        (fun r : ℕ ↦ c * q ^ r) j =
      (-1 : K) ^ j /
        (c ^ n * q ^ (j.choose 2 + j * (n - j)) *
          (geometricQPochhammer q j * geometricQPochhammer q (n - j))) := by
  have hjmem : j ∈ range (n + 1) := Finset.mem_range.mpr (by omega)
  have hscaled :
      (∏ r ∈ (range (n + 1)).erase j,
        (c * q ^ j - c * q ^ r)) =
        c ^ n * ∏ r ∈ (range (n + 1)).erase j, (q ^ j - q ^ r) := by
    calc
      (∏ r ∈ (range (n + 1)).erase j,
          (c * q ^ j - c * q ^ r)) =
          ∏ r ∈ (range (n + 1)).erase j, c * (q ^ j - q ^ r) := by
        apply Finset.prod_congr rfl
        intro r _hr
        ring
      _ = (∏ _r ∈ (range (n + 1)).erase j, c) *
          ∏ r ∈ (range (n + 1)).erase j, (q ^ j - q ^ r) := by
        rw [Finset.prod_mul_distrib]
      _ = c ^ n *
          ∏ r ∈ (range (n + 1)).erase j, (q ^ j - q ^ r) := by
        simp only [Finset.prod_const, Finset.card_erase_of_mem hjmem,
          Finset.card_range, Nat.add_sub_cancel]
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib, hscaled,
    prod_erase_pow_sub_pow q hj]
  simp only [← geometricQPochhammer_eq_finiteQPochhammerIn]
  let A : K := c ^ n * q ^ (j.choose 2 + j * (n - j)) *
    (geometricQPochhammer q j * geometricQPochhammer q (n - j))
  have hden :
      c ^ n * ((-1 : K) ^ j * q ^ (j.choose 2 + j * (n - j)) *
        (geometricQPochhammer q j * geometricQPochhammer q (n - j))) =
        (-1 : K) ^ j * A := by
    dsimp only [A]
    ring
  have hsign : ((-1 : K) ^ j)⁻¹ = (-1 : K) ^ j := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [hden, mul_inv, hsign, div_eq_mul_inv]

/-- **Explicit geometric Lagrange--Rvachev decoder entry.**  This is the
manuscript decoder formula before the separate finite Rvachev synthesis
theorem is applied: the Gaussian q-Pochhammer prefactor multiplies the finite
even reciprocal-moment sum in the translated nodes other than `cq^j`.
The hypotheses `0 < q < 1`, `0 < c ≤ 1`, and `M = 2^n` from the analytic
application are unnecessary for this algebraic identity. -/
theorem geometric_lagrangeRvachevDecoder_eq
    (c q : ℝ) (n j : ℕ) (hj : j ≤ n) (M : ℕ) (k : ℤ) :
    lagrangeRvachevDecoder (range (n + 1))
        (fun r : ℕ ↦ c * q ^ r) M k j =
      ((-1 : ℝ) ^ j /
        (c ^ n * q ^ (j.choose 2 + j * (n - j)) *
          (geometricQPochhammer q j * geometricQPochhammer q (n - j)))) *
        ∑ r ∈ range (n / 2 + 1),
          (rvachevReciprocalMomentRat (2 * r) : ℝ) *
            elementarySymmetricEval
              (fun s : ↥((range (n + 1)).erase j) ↦
                (k : ℝ) / (M : ℝ) - c * q ^ (s : ℕ))
              (n - 2 * r) := by
  rw [lagrangeRvachevDecoder_eq_nodalWeight_mul_sum
    (range (n + 1)) (fun r : ℕ ↦ c * q ^ r) (by simpa using hj) M k,
    geometric_nodalWeight_eq_geometricQPochhammer c q n j hj]
  simp only [Finset.card_range, Nat.add_sub_cancel]

end

end Fabius
