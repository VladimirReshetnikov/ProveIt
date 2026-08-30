import FabiusFunction.GramStieltjes

/-!
# Finite Jacobi recurrence for a scalar moment sequence

This module continues the measure-free Gram--Stieltjes algebra of
`FiniteMomentGram.lean` and `GramStieltjes.lean`.  For an arbitrary scalar
moment sequence over a field, it defines

* `gramStieltjesNorm`, the quotient of consecutive Hankel determinants;
* `gramStieltjesJacobiDiagonal`, the diagonal finite Jacobi coefficient;
* `gramStieltjesJacobiSubdiagonal`, the quotient of consecutive norms.

A nonzero order-one minor gives the degree-zero recurrence.  If the three
Hankel minors of orders `n`, `n + 1`, and `n + 2` are nonzero, the three
consecutive monic Gram--Stieltjes polynomials satisfy every higher exact
three-term recurrence.  The subdiagonal coefficient is also identified with
the usual cross-ratio of four Hankel factors (three distinct minors).

Everything is finite algebra.  No measure representation, positivity, root
theorem, quadrature rule, infinite continued fraction, or convergence
assertion is used.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## Pairing lemmas -/

/-- Multiplication by `X` may be shifted from one argument of a moment pairing
to the other. -/
theorem momentPairing_X_mul_left {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (p q : R[X]) :
    momentPairing moment (Polynomial.X * p) q =
      momentPairing moment p (Polynomial.X * q) := by
  simp only [momentPairing_apply]
  congr 1
  ring

/-- Vanishing against all pure powers below `n` implies vanishing against
every polynomial of degree below `n`. -/
theorem momentPairing_eq_zero_of_forall_X_pow {K : Type*} [Field K]
    (moment : ℕ → K) {p q : K[X]} {n : ℕ}
    (hpow : ∀ i : Fin n,
      momentPairing moment p (Polynomial.X ^ (i : ℕ)) = 0)
    (hq : q.natDegree < n) :
    momentPairing moment p q = 0 := by
  by_cases hn : n = 0
  · omega
  calc
    momentPairing moment p q =
        ∑ i ∈ range n, q.coeff i *
          momentPairing moment p (Polynomial.X ^ i) := by
      conv_lhs => rw [q.as_sum_range_C_mul_X_pow' hq]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hpow ⟨i, Finset.mem_range.mp hi⟩, mul_zero]

private theorem momentPairing_C_mul_left {K : Type*} [Field K]
    (moment : ℕ → K) (a : K) (p q : K[X]) :
    momentPairing moment (Polynomial.C a * p) q =
      a * momentPairing moment p q := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, LinearMap.smul_apply,
    smul_eq_mul]

/-! ## Finite Jacobi data -/

/-- The self-pairing candidate of the degree-`n` monic Gram--Stieltjes
polynomial: the quotient of the order-`n+1` and order-`n` Hankel
determinants. -/
def gramStieltjesNorm {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) : K :=
  momentHankelDet moment (n + 1) / momentHankelDet moment n

/-- Pairing the degree-`n` Gram--Stieltjes polynomial with its leading pure
power gives its finite norm quotient.  This identity does not require a
nonvanishing assumption. -/
theorem momentPairing_gramStieltjesPolynomial_X_pow_eq_norm
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ) :
    momentPairing moment (gramStieltjesPolynomial moment n)
        (Polynomial.X ^ n) = gramStieltjesNorm moment n := by
  rw [gramStieltjesPolynomial, ← Polynomial.smul_eq_C_mul, map_smul,
    LinearMap.smul_apply, smul_eq_mul,
    momentPairing_gramStieltjesNumerator_X_pow_eq_det]
  rw [gramStieltjesNorm, div_eq_mul_inv, mul_comm]

/-- When the order-`n` Hankel determinant is nonzero, the self-pairing of the
degree-`n` Gram--Stieltjes polynomial is its finite norm quotient. -/
theorem momentPairing_gramStieltjesPolynomial_self_eq_norm
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ)
    (hdet : momentHankelDet moment n ≠ 0) :
    momentPairing moment (gramStieltjesPolynomial moment n)
        (gramStieltjesPolynomial moment n) =
      gramStieltjesNorm moment n := by
  simpa only [gramStieltjesNorm] using
    momentPairing_gramStieltjesPolynomial_self moment n hdet

/-- Two consecutive nonzero Hankel determinants give a nonzero finite
Gram--Stieltjes norm. -/
theorem gramStieltjesNorm_ne_zero {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ)
    (hdet : momentHankelDet moment n ≠ 0)
    (hdet' : momentHankelDet moment (n + 1) ≠ 0) :
    gramStieltjesNorm moment n ≠ 0 :=
  div_ne_zero hdet' hdet

/-- The diagonal finite Jacobi coefficient of the degree-`n`
Gram--Stieltjes polynomial. -/
def gramStieltjesJacobiDiagonal {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) : K :=
  momentPairing moment
      (Polynomial.X * gramStieltjesPolynomial moment n)
      (gramStieltjesPolynomial moment n) /
    gramStieltjesNorm moment n

/-- The subdiagonal finite Jacobi coefficient coupling degrees `n+1` and
`n`: the quotient of their consecutive Gram--Stieltjes norms. -/
def gramStieltjesJacobiSubdiagonal {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) : K :=
  gramStieltjesNorm moment (n + 1) / gramStieltjesNorm moment n

/-- The finite Jacobi subdiagonal is the Hankel cross-ratio
`Delta_(n+2) * Delta_n / Delta_(n+1)^2`. -/
theorem gramStieltjesJacobiSubdiagonal_eq_det_ratio
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ) :
    gramStieltjesJacobiSubdiagonal moment n =
      momentHankelDet moment (n + 2) * momentHankelDet moment n /
        momentHankelDet moment (n + 1) ^ 2 := by
  by_cases hdet : momentHankelDet moment n = 0
  · simp [gramStieltjesJacobiSubdiagonal, gramStieltjesNorm, hdet]
  by_cases hdet' : momentHankelDet moment (n + 1) = 0
  · simp [gramStieltjesJacobiSubdiagonal, gramStieltjesNorm, hdet']
  rw [gramStieltjesJacobiSubdiagonal, gramStieltjesNorm,
    gramStieltjesNorm]
  field_simp [hdet, hdet']

/-! ## The finite three-term recurrence -/

/-- A nonzero order-one Hankel minor gives the degree-zero finite Jacobi
recurrence. -/
theorem gramStieltjesPolynomial_three_term_zero
    {K : Type*} [Field K] (moment : ℕ → K)
    (hdet : momentHankelDet moment 1 ≠ 0) :
    Polynomial.X * gramStieltjesPolynomial moment 0 =
      gramStieltjesPolynomial moment 1 +
        Polynomial.C (gramStieltjesJacobiDiagonal moment 0) *
          gramStieltjesPolynomial moment 0 := by
  let P : ℕ → K[X] := fun k ↦ gramStieltjesPolynomial moment k
  let alpha : K := gramStieltjesJacobiDiagonal moment 0
  let r : K[X] :=
    Polynomial.X * P 0 - P 1 - Polynomial.C alpha * P 0

  have hdet₀ : momentHankelDet moment 0 ≠ 0 := by
    simpa only [momentHankelDet_zero] using (one_ne_zero : (1 : K) ≠ 0)
  have hP₀ : Polynomial.IsMonicOfDegree (P 0) 0 :=
    gramStieltjesPolynomial_isMonicOfDegree moment 0 hdet₀
  have hP₁ : Polynomial.IsMonicOfDegree (P 1) 1 :=
    gramStieltjesPolynomial_isMonicOfDegree moment 1 hdet
  have hP₀_eq : P 0 = 1 :=
    Polynomial.isMonicOfDegree_zero_iff.mp hP₀
  have hXP₀ : Polynomial.IsMonicOfDegree (Polynomial.X * P 0) 1 := by
    simpa only [Nat.add_zero] using
      (Polynomial.isMonicOfDegree_X K).mul hP₀

  have hnorm₀ : momentPairing moment (P 0) (P 0) =
      gramStieltjesNorm moment 0 :=
    momentPairing_gramStieltjesPolynomial_self_eq_norm
      moment 0 hdet₀
  have hnorm₀_ne : gramStieltjesNorm moment 0 ≠ 0 :=
    gramStieltjesNorm_ne_zero moment 0 hdet₀ hdet
  have hP₁P₀ : momentPairing moment (P 1) (P 0) = 0 := by
    apply momentPairing_gramStieltjesPolynomial_eq_zero
    rw [hP₀.natDegree_eq]
    omega
  have halpha : alpha * momentPairing moment (P 0) (P 0) =
      momentPairing moment (Polynomial.X * P 0) (P 0) := by
    rw [hnorm₀]
    dsimp only [alpha]
    rw [gramStieltjesJacobiDiagonal]
    exact div_mul_cancel₀ _ hnorm₀_ne
  have hrP₀ : momentPairing moment r (P 0) = 0 := by
    simp only [r, map_sub, LinearMap.sub_apply,
      momentPairing_C_mul_left]
    rw [hP₁P₀, halpha]
    ring
  have hrPow : ∀ i : Fin 1,
      momentPairing moment r (Polynomial.X ^ (i : ℕ)) = 0 := by
    intro i
    have hi : (i : ℕ) = 0 := by omega
    simpa only [hi, pow_zero, hP₀_eq] using hrP₀

  have hdeg_first :
      (Polynomial.X * P 0 - P 1).natDegree < 1 :=
    hXP₀.natDegree_sub_lt one_ne_zero hP₁
  have hdeg_alpha :
      (Polynomial.C alpha * P 0).natDegree < 1 :=
    (Polynomial.natDegree_C_mul_le alpha (P 0)).trans_lt
      (by rw [hP₀.natDegree_eq]; omega)
  have hrdeg : r.natDegree < 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt hdeg_first hdeg_alpha)
  have hrmem : r ∈ Polynomial.degreeLT K 1 := by
    rw [Polynomial.mem_degreeLT]
    by_cases hr₀ : r = 0
    · rw [hr₀, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree hr₀, Nat.cast_lt]
      exact hrdeg
  let d : Polynomial.degreeLT K 1 := ⟨r, hrmem⟩
  have hnondeg := (finiteMomentPairing_nondegenerate_iff moment 1).2 hdet
  have hd : d = 0 := hnondeg.1 d fun q ↦ by
    have hqdeg : (q : K[X]).natDegree < 1 := by
      by_cases hq₀ : (q : K[X]) = 0
      · simp [hq₀]
      · have hqmem := q.property
        rw [Polynomial.mem_degreeLT,
          Polynomial.degree_eq_natDegree hq₀, Nat.cast_lt] at hqmem
        exact hqmem
    change momentPairing moment r (q : K[X]) = 0
    exact momentPairing_eq_zero_of_forall_X_pow moment hrPow hqdeg
  have hr₀ : r = 0 := Subtype.ext_iff.mp hd
  dsimp only [r, P, alpha] at hr₀ ⊢
  apply sub_eq_zero.mp
  calc
    Polynomial.X * gramStieltjesPolynomial moment 0 -
        (gramStieltjesPolynomial moment 1 +
          Polynomial.C (gramStieltjesJacobiDiagonal moment 0) *
            gramStieltjesPolynomial moment 0) =
      Polynomial.X * gramStieltjesPolynomial moment 0 -
        gramStieltjesPolynomial moment 1 -
          Polynomial.C (gramStieltjesJacobiDiagonal moment 0) *
            gramStieltjesPolynomial moment 0 := by ring
    _ = 0 := hr₀

/-- Three consecutive nonzero Hankel minors give the finite Jacobi
three-term recurrence for the corresponding monic Gram--Stieltjes
polynomials. -/
theorem gramStieltjesPolynomial_three_term
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ)
    (hdet : momentHankelDet moment n ≠ 0)
    (hdet' : momentHankelDet moment (n + 1) ≠ 0)
    (hdet'' : momentHankelDet moment (n + 2) ≠ 0) :
    Polynomial.X * gramStieltjesPolynomial moment (n + 1) =
      gramStieltjesPolynomial moment (n + 2) +
        Polynomial.C (gramStieltjesJacobiDiagonal moment (n + 1)) *
          gramStieltjesPolynomial moment (n + 1) +
        Polynomial.C (gramStieltjesJacobiSubdiagonal moment n) *
          gramStieltjesPolynomial moment n := by
  let P : ℕ → K[X] := fun k ↦ gramStieltjesPolynomial moment k
  let alpha : K := gramStieltjesJacobiDiagonal moment (n + 1)
  let beta : K := gramStieltjesJacobiSubdiagonal moment n
  let r : K[X] :=
    Polynomial.X * P (n + 1) - P (n + 2) -
      Polynomial.C alpha * P (n + 1) - Polynomial.C beta * P n

  have hP₀ : Polynomial.IsMonicOfDegree (P n) n := by
    exact gramStieltjesPolynomial_isMonicOfDegree moment n hdet
  have hP₁ : Polynomial.IsMonicOfDegree (P (n + 1)) (n + 1) := by
    exact gramStieltjesPolynomial_isMonicOfDegree moment (n + 1) hdet'
  have hP₂ : Polynomial.IsMonicOfDegree (P (n + 2)) (n + 2) := by
    exact gramStieltjesPolynomial_isMonicOfDegree moment (n + 2) hdet''
  have hXP₀ : Polynomial.IsMonicOfDegree
      (Polynomial.X * P n) (n + 1) := by
    simpa only [Nat.one_add] using
      (Polynomial.isMonicOfDegree_X K).mul hP₀
  have hXP₁ : Polynomial.IsMonicOfDegree
      (Polynomial.X * P (n + 1)) (n + 2) := by
    simpa only [Nat.one_add, Nat.add_assoc] using
      (Polynomial.isMonicOfDegree_X K).mul hP₁

  have hnorm₀ :
      momentPairing moment (P n) (P n) =
        gramStieltjesNorm moment n := by
    exact momentPairing_gramStieltjesPolynomial_self_eq_norm
      moment n hdet
  have hnorm₁ :
      momentPairing moment (P (n + 1)) (P (n + 1)) =
        gramStieltjesNorm moment (n + 1) := by
    exact momentPairing_gramStieltjesPolynomial_self_eq_norm
      moment (n + 1) hdet'
  have hnorm₀_ne : gramStieltjesNorm moment n ≠ 0 :=
    gramStieltjesNorm_ne_zero moment n hdet hdet'
  have hnorm₁_ne : gramStieltjesNorm moment (n + 1) ≠ 0 :=
    gramStieltjesNorm_ne_zero moment (n + 1) hdet' hdet''

  have hP₁P₀ : momentPairing moment (P (n + 1)) (P n) = 0 := by
    apply momentPairing_gramStieltjesPolynomial_eq_zero
    rw [hP₀.natDegree_eq]
    omega
  have hP₀P₁ : momentPairing moment (P n) (P (n + 1)) = 0 := by
    rw [(momentPairing_isSymm moment).eq (P n) (P (n + 1)), hP₁P₀]
  have hP₂P₀ : momentPairing moment (P (n + 2)) (P n) = 0 := by
    apply momentPairing_gramStieltjesPolynomial_eq_zero
    rw [hP₀.natDegree_eq]
    omega
  have hP₂P₁ :
      momentPairing moment (P (n + 2)) (P (n + 1)) = 0 := by
    apply momentPairing_gramStieltjesPolynomial_eq_zero
    rw [hP₁.natDegree_eq]
    omega

  have hXP₁P₀ :
      momentPairing moment (Polynomial.X * P (n + 1)) (P n) =
        gramStieltjesNorm moment (n + 1) := by
    rw [momentPairing_X_mul_left]
    have hdiff :
        (Polynomial.X * P n - P (n + 1)).natDegree < n + 1 :=
      hXP₀.natDegree_sub_lt (by omega) hP₁
    have horth : momentPairing moment (P (n + 1))
        (Polynomial.X * P n - P (n + 1)) = 0 :=
      momentPairing_gramStieltjesPolynomial_eq_zero
        moment (n + 1) _ hdiff
    have hsplit : Polynomial.X * P n =
        P (n + 1) + (Polynomial.X * P n - P (n + 1)) := by
      ring
    rw [hsplit, map_add, horth, add_zero, hnorm₁]

  have halpha : alpha *
      momentPairing moment (P (n + 1)) (P (n + 1)) =
        momentPairing moment (Polynomial.X * P (n + 1))
          (P (n + 1)) := by
    rw [hnorm₁]
    dsimp only [alpha]
    rw [gramStieltjesJacobiDiagonal]
    exact div_mul_cancel₀ _ hnorm₁_ne
  have hbeta : beta * momentPairing moment (P n) (P n) =
      gramStieltjesNorm moment (n + 1) := by
    rw [hnorm₀]
    dsimp only [beta]
    rw [gramStieltjesJacobiSubdiagonal]
    exact div_mul_cancel₀ _ hnorm₀_ne

  have hrP₁ : momentPairing moment r (P (n + 1)) = 0 := by
    simp only [r, map_sub, LinearMap.sub_apply,
      momentPairing_C_mul_left]
    rw [hP₂P₁, hP₀P₁, halpha]
    ring
  have hrP₀ : momentPairing moment r (P n) = 0 := by
    simp only [r, map_sub, LinearMap.sub_apply,
      momentPairing_C_mul_left]
    rw [hXP₁P₀, hP₂P₀, hP₁P₀, hbeta]
    ring

  have hrPow_lt : ∀ j < n,
      momentPairing moment r (Polynomial.X ^ j) = 0 := by
    intro j hj
    have hXP : momentPairing moment (Polynomial.X * P (n + 1))
        (Polynomial.X ^ j) = 0 := by
      rw [momentPairing_X_mul_left]
      simpa only [pow_succ'] using
        momentPairing_gramStieltjesPolynomial_X_pow_eq_zero
          moment (n + 1) ⟨j + 1, by omega⟩
    have hP₂X : momentPairing moment (P (n + 2))
        (Polynomial.X ^ j) = 0 :=
      momentPairing_gramStieltjesPolynomial_X_pow_eq_zero
        moment (n + 2) ⟨j, by omega⟩
    have hP₁X : momentPairing moment (P (n + 1))
        (Polynomial.X ^ j) = 0 :=
      momentPairing_gramStieltjesPolynomial_X_pow_eq_zero
        moment (n + 1) ⟨j, by omega⟩
    have hP₀X : momentPairing moment (P n)
        (Polynomial.X ^ j) = 0 :=
      momentPairing_gramStieltjesPolynomial_X_pow_eq_zero
        moment n ⟨j, hj⟩
    simp only [r, map_sub, LinearMap.sub_apply,
      momentPairing_C_mul_left]
    rw [hXP, hP₂X, hP₁X, hP₀X]
    ring

  have hrXn : momentPairing moment r (Polynomial.X ^ n) = 0 := by
    by_cases hn : n = 0
    · subst n
      have hP₀_eq : P 0 = 1 :=
        Polynomial.isMonicOfDegree_zero_iff.mp hP₀
      simpa only [pow_zero, hP₀_eq] using hrP₀
    · rcases hP₀.exists_natDegree_lt hn with ⟨q, hq, hqdeg⟩
      have hrq : momentPairing moment r q = 0 :=
        momentPairing_eq_zero_of_forall_X_pow moment
          (fun i ↦ hrPow_lt (i : ℕ) i.isLt) hqdeg
      rw [hq, map_add, hrq, add_zero] at hrP₀
      exact hrP₀

  have hrXn1 :
      momentPairing moment r (Polynomial.X ^ (n + 1)) = 0 := by
    rcases hP₁.exists_natDegree_lt (by omega) with ⟨q, hq, hqdeg⟩
    have hpow : ∀ i : Fin (n + 1),
        momentPairing moment r (Polynomial.X ^ (i : ℕ)) = 0 := by
      intro i
      by_cases hi : (i : ℕ) < n
      · exact hrPow_lt (i : ℕ) hi
      · have hin : (i : ℕ) = n := by omega
        simpa only [hin] using hrXn
    have hrq : momentPairing moment r q = 0 :=
      momentPairing_eq_zero_of_forall_X_pow moment hpow hqdeg
    rw [hq, map_add, hrq, add_zero] at hrP₁
    exact hrP₁

  have hrPow : ∀ i : Fin (n + 2),
      momentPairing moment r (Polynomial.X ^ (i : ℕ)) = 0 := by
    intro i
    by_cases hi : (i : ℕ) < n
    · exact hrPow_lt (i : ℕ) hi
    · by_cases hin : (i : ℕ) = n
      · simpa only [hin] using hrXn
      · have hi₁ : (i : ℕ) = n + 1 := by omega
        simpa only [hi₁] using hrXn1

  have hdeg_first :
      (Polynomial.X * P (n + 1) - P (n + 2)).natDegree < n + 2 :=
    hXP₁.natDegree_sub_lt (by omega) hP₂
  have hdeg_alpha :
      (Polynomial.C alpha * P (n + 1)).natDegree < n + 2 :=
    (Polynomial.natDegree_C_mul_le alpha (P (n + 1))).trans_lt
      (by rw [hP₁.natDegree_eq]; omega)
  have hdeg_beta :
      (Polynomial.C beta * P n).natDegree < n + 2 :=
    (Polynomial.natDegree_C_mul_le beta (P n)).trans_lt
      (by rw [hP₀.natDegree_eq]; omega)
  have hdeg_second :
      (Polynomial.X * P (n + 1) - P (n + 2) -
        Polynomial.C alpha * P (n + 1)).natDegree < n + 2 :=
    (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt hdeg_first hdeg_alpha)
  have hrdeg : r.natDegree < n + 2 := by
    exact (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt hdeg_second hdeg_beta)

  have hrmem : r ∈ Polynomial.degreeLT K (n + 2) := by
    rw [Polynomial.mem_degreeLT]
    by_cases hr₀ : r = 0
    · rw [hr₀, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree hr₀, Nat.cast_lt]
      exact hrdeg
  let d : Polynomial.degreeLT K (n + 2) := ⟨r, hrmem⟩
  have hnondeg :=
    (finiteMomentPairing_nondegenerate_iff moment (n + 2)).2 hdet''
  have hd : d = 0 := hnondeg.1 d fun q ↦ by
    have hqdeg : (q : K[X]).natDegree < n + 2 := by
      by_cases hq₀ : (q : K[X]) = 0
      · simp [hq₀]
      · have hqmem := q.property
        rw [Polynomial.mem_degreeLT,
          Polynomial.degree_eq_natDegree hq₀, Nat.cast_lt] at hqmem
        exact hqmem
    change momentPairing moment r (q : K[X]) = 0
    exact momentPairing_eq_zero_of_forall_X_pow moment hrPow hqdeg
  have hr₀ : r = 0 := Subtype.ext_iff.mp hd
  dsimp only [r, P, alpha, beta] at hr₀ ⊢
  apply sub_eq_zero.mp
  calc
    Polynomial.X * gramStieltjesPolynomial moment (n + 1) -
        (gramStieltjesPolynomial moment (n + 2) +
          Polynomial.C (gramStieltjesJacobiDiagonal moment (n + 1)) *
            gramStieltjesPolynomial moment (n + 1) +
          Polynomial.C (gramStieltjesJacobiSubdiagonal moment n) *
            gramStieltjesPolynomial moment n) =
      Polynomial.X * gramStieltjesPolynomial moment (n + 1) -
        gramStieltjesPolynomial moment (n + 2) -
          Polynomial.C (gramStieltjesJacobiDiagonal moment (n + 1)) *
            gramStieltjesPolynomial moment (n + 1) -
          Polynomial.C (gramStieltjesJacobiSubdiagonal moment n) *
            gramStieltjesPolynomial moment n := by ring
    _ = 0 := hr₀

end

end Fabius
