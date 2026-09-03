import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.QBinomialVandermonde
import FabiusFunction.GeometricQBinomialLagrange
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Jacobi's triple product and Euler's pentagonal number theorem

Jacobi's triple product identity

`∑_{k ∈ ℤ} (-1)^k q^{k(k-1)/2} z^k = (z;q)_∞ (q/z;q)_∞ (q;q)_∞`

is proved here as the stable limit of an **exact polynomial identity**, the
finite triple product

`(z;q)_N (q/z;q)_N = ∑_{k=-N}^{N} (-1)^k q^{k(k-1)/2} [2N, N+k]_q z^k`.

The finite identity is pure algebra: multiply the finite `q`-binomial
expansions of `(z;q)_N` and of `z^N (q/z;q)_N = ∏_{j<N} (z - q^{j+1})`, and
recognize the coefficient of each power of `z` as a shifted central
`q`-Vandermonde convolution.  It holds in every commutative ring (in its
polynomial form) and needs no convergence hypothesis.  Its only analytic
content is the single limit `[2N, N+k]_q → 1/(q;q)_∞`, under the uniform
Gaussian majorant of `QBinomialTheoremInfinite`; Tannery's theorem then
delivers Jacobi's identity over every complete normed field.

Euler's pentagonal number theorem `(q;q)_∞ = ∑_k (-1)^k q^{k(3k-1)/2}` is the
specialization `q ↦ q³`, `z ↦ q`, the product side collapsing by dissection
into residue classes modulo three.

## Main declarations

* `thetaExponent`: the exponent `k(k-1)/2 ∈ ℕ` for `k ∈ ℤ`, with
  `two_mul_thetaExponent`, `thetaExponent_natCast`, `thetaExponent_neg_natCast`.
* `finite_triple_product_poly`: the polynomial form of the finite identity,
  over every commutative ring.
* `finite_triple_product`: the Laurent form over a field, for `z ≠ 0`.
* `tendsto_gaussianBinomialInt_central`: `[2N, N+k]_q → 1/(q;q)_∞`.
* `hasSum_jacobi_triple_product`, `hasSum_jacobi_triple_product'`: Jacobi's
  identity in its `(z;q)_∞(q/z;q)_∞` and `(-z;q)_∞(-q/z;q)_∞` forms.
* `pentagonalExponent`, `hasSum_pentagonal`: Euler's pentagonal number
  theorem.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## The theta exponent `k(k-1)/2` on the integers -/

/-- The theta exponent `k(k-1)/2 ∈ ℕ`, defined for every integer `k`.  For
`k = n ≥ 0` it is `C(n,2)`; for `k = -n` it is `C(n+1,2)`. -/
def thetaExponent (k : ℤ) : ℕ := (k * (k - 1) / 2).toNat

/-- `k(k-1)` is even. -/
theorem two_dvd_mul_sub_one (k : ℤ) : (2 : ℤ) ∣ k * (k - 1) := by
  have h := Int.even_mul_succ_self (k - 1)
  rw [sub_add_cancel, mul_comm] at h
  exact even_iff_two_dvd.mp h

/-- `k(k-1) ≥ 0` for every integer `k`. -/
theorem mul_sub_one_nonneg (k : ℤ) : 0 ≤ k * (k - 1) := by
  rcases le_or_gt 1 k with h | h
  · exact mul_nonneg (by omega) (by omega)
  · have h0 : k ≤ 0 := by omega
    nlinarith

/-- The defining property of the theta exponent: `2 e(k) = k(k-1)`. -/
theorem two_mul_thetaExponent (k : ℤ) :
    (2 : ℤ) * (thetaExponent k : ℤ) = k * (k - 1) := by
  unfold thetaExponent
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg (mul_sub_one_nonneg k) (by norm_num))]
  exact Int.mul_ediv_cancel' (two_dvd_mul_sub_one k)

/-- On nonnegative integers the theta exponent is `C(n,2)`. -/
theorem thetaExponent_natCast (n : ℕ) : thetaExponent n = n.choose 2 := by
  have h := two_mul_thetaExponent n
  have h2 : (2 : ℤ) * (n.choose 2 : ℤ) + n = (n : ℤ) ^ 2 := by
    exact_mod_cast Fabius.two_mul_choose_two_add n
  have h3 : (2 : ℤ) * (thetaExponent n : ℤ) = 2 * (n.choose 2 : ℤ) := by
    linear_combination h - h2
  omega

/-- On negative integers the theta exponent is `e(-n) = C(n+1,2)`. -/
theorem thetaExponent_neg_natCast (n : ℕ) :
    thetaExponent (-(n : ℤ)) = (n + 1).choose 2 := by
  have h := two_mul_thetaExponent (-(n : ℤ))
  have h2 : (2 : ℤ) * ((n + 1).choose 2 : ℤ) + ((n : ℤ) + 1) = ((n : ℤ) + 1) ^ 2 := by
    exact_mod_cast Fabius.two_mul_choose_two_add (n + 1)
  have h3 : (2 : ℤ) * (thetaExponent (-(n : ℤ)) : ℤ) = 2 * ((n + 1).choose 2 : ℤ) := by
    linear_combination h - h2
  omega

/-- The exponent bookkeeping of the finite triple product:
`C(i,2) + C(u+1,2) = e(i-u) + u·i`. -/
theorem choose_two_add_choose_two_succ_eq (i u : ℕ) :
    i.choose 2 + (u + 1).choose 2 = thetaExponent ((i : ℤ) - u) + u * i := by
  have h1 : (2 : ℤ) * (i.choose 2 : ℤ) + i = (i : ℤ) ^ 2 := by
    exact_mod_cast Fabius.two_mul_choose_two_add i
  have h2 : (2 : ℤ) * ((u + 1).choose 2 : ℤ) + ((u : ℤ) + 1) = ((u : ℤ) + 1) ^ 2 := by
    exact_mod_cast Fabius.two_mul_choose_two_add (u + 1)
  have h3 := two_mul_thetaExponent ((i : ℤ) - u)
  have key : (2 : ℤ) * ((i.choose 2 : ℤ) + ((u + 1).choose 2 : ℤ)) =
      2 * ((thetaExponent ((i : ℤ) - u) : ℤ) + (u : ℤ) * i) := by
    linear_combination h1 + h2 - h3
  have key' := mul_left_cancel₀ (two_ne_zero' ℤ) key
  exact_mod_cast key'

/-! ## The finite triple product -/

section FinitePolynomial

variable {R : Type*} [CommRing R]

/-- Cauchy product of two finite expansions of length `N + 1` whose
coefficient sequences vanish beyond `N`. -/
theorem sum_mul_sum_eq_sum_antidiagonal (a b : ℕ → R) (N : ℕ) (z : R)
    (ha : ∀ i, N < i → a i = 0) (hb : ∀ j, N < j → b j = 0) :
    (∑ i ∈ range (N + 1), a i * z ^ i) * (∑ j ∈ range (N + 1), b j * z ^ j) =
      ∑ m ∈ range (2 * N + 1), (∑ ij ∈ antidiagonal m, a ij.1 * b ij.2) * z ^ m := by
  classical
  let P : Polynomial R := ∑ i ∈ range (N + 1), Polynomial.C (a i) * Polynomial.X ^ i
  let Q : Polynomial R := ∑ j ∈ range (N + 1), Polynomial.C (b j) * Polynomial.X ^ j
  have hcoeff : ∀ (c : ℕ → R), (∀ i, N < i → c i = 0) → ∀ n,
      (∑ i ∈ range (N + 1), Polynomial.C (c i) * Polynomial.X ^ i).coeff n = c n := by
    intro c hc n
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range, not_lt] at h
      exact (hc n h).symm
  have hPc : ∀ n, P.coeff n = a n := hcoeff a ha
  have hQc : ∀ n, Q.coeff n = b n := hcoeff b hb
  have hPe : P.eval z = ∑ i ∈ range (N + 1), a i * z ^ i := by
    simp [P, Polynomial.eval_finsetSum]
  have hQe : Q.eval z = ∑ j ∈ range (N + 1), b j * z ^ j := by
    simp [Q, Polynomial.eval_finsetSum]
  have hdegP : P.natDegree ≤ N :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hdegQ : Q.natDegree ≤ N :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hdeg : (P * Q).natDegree < 2 * N + 1 := by
    have := Polynomial.natDegree_mul_le (p := P) (q := Q)
    omega
  rw [← hPe, ← hQe, ← Polynomial.eval_mul, Polynomial.eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_mul]
  congr 1
  exact Finset.sum_congr rfl fun ij _ => by rw [hPc, hQc]

/-- The coefficient pairing behind the finite triple product: for
`i + j = m` with `i, j ≤ N`, the product of the `i`-th coefficient of
`(z;q)_N` and the `j`-th coefficient of `∏_{j<N}(z - q^{j+1})` is the
`(N-j)`-th summand of the shifted central `q`-Vandermonde convolution for
`[2N, m]_q`, times the sign `(-1)^{N+m}` and the power `q^{e(m-N)}`. -/
theorem thetaCoeff_pair_eq (q : R) {N i j m : ℕ} (_hi : i ≤ N) (hj : j ≤ N)
    (hm : i + j = m) :
    ((-1 : R) ^ i * q ^ i.choose 2 * gaussianBinomial q N i) *
        geometricQBinomialWeightNumerator q N j =
      (-1 : R) ^ (N + m) * q ^ thetaExponent ((m : ℤ) - N) *
        (q ^ ((N - j) * (((N - j : ℕ) : ℤ) + ((m : ℤ) - N)).toNat) *
          gaussianBinomial q N (N - j) *
            gaussianBinomialInt q N (((N - j : ℕ) : ℤ) + ((m : ℤ) - N))) := by
  have hidx : ((N - j : ℕ) : ℤ) + ((m : ℤ) - N) = (i : ℤ) := by omega
  have htoNat : (((N - j : ℕ) : ℤ) + ((m : ℤ) - N)).toNat = i := by omega
  rw [htoNat, hidx, gaussianBinomialInt_ofNat, gaussianBinomial_symm q hj,
    geometricQBinomialWeightNumerator_eq_forward_of_le q hj]
  -- signs: `(-1)^i (-1)^(N-j) = (-1)^(N+m)`
  have hsign : (-1 : R) ^ (N + m) = (-1) ^ i * (-1) ^ (N - j) := by
    rw [← pow_add]
    have hexp : N + m = (i + (N - j)) + 2 * j := by omega
    rw [hexp, pow_add, pow_mul]
    simp
  -- exponents: `C(i,2) + C(N-j+1,2) = e(m-N) + (N-j)·i`
  have hexp : q ^ i.choose 2 * q ^ ((N - j + 1).choose 2) =
      q ^ thetaExponent ((m : ℤ) - N) * q ^ ((N - j) * i) := by
    have harg : (i : ℤ) - ((N - j : ℕ) : ℤ) = (m : ℤ) - N := by omega
    rw [← pow_add, ← pow_add, choose_two_add_choose_two_succ_eq i (N - j), harg]
  calc ((-1 : R) ^ i * q ^ i.choose 2 * gaussianBinomial q N i) *
        ((-1) ^ (N - j) * q ^ ((N - j + 1).choose 2) * gaussianBinomial q N j)
      = ((-1) ^ i * (-1) ^ (N - j)) * (q ^ i.choose 2 * q ^ ((N - j + 1).choose 2)) *
          (gaussianBinomial q N j * gaussianBinomial q N i) := by ring
    _ = (-1 : R) ^ (N + m) * q ^ thetaExponent ((m : ℤ) - N) *
        (q ^ ((N - j) * i) * gaussianBinomial q N j * gaussianBinomial q N i) := by
      rw [hsign, hexp]
      ring

/-- **The coefficient identity.**  The Cauchy product of the coefficients of
`(z;q)_N` and of `∏_{j<N} (z - q^{j+1})` at total degree `m` is
`(-1)^{N+m} q^{e(m-N)} [2N, m]_q`. -/
theorem sum_antidiagonal_thetaCoeff (q : R) (N m : ℕ) :
    ∑ ij ∈ antidiagonal m,
        ((-1 : R) ^ ij.1 * q ^ ij.1.choose 2 * gaussianBinomial q N ij.1) *
          geometricQBinomialWeightNumerator q N ij.2 =
      (-1 : R) ^ (N + m) * q ^ thetaExponent ((m : ℤ) - N) * gaussianBinomial q (2 * N) m := by
  classical
  have hV := gaussianBinomial_two_mul_int_shifted_central q N ((m : ℤ) - N)
  rw [show (N : ℤ) + ((m : ℤ) - N) = (m : ℤ) by ring, gaussianBinomialInt_ofNat] at hV
  rw [hV, Finset.mul_sum]
  -- both sides vanish unless `i, j ≤ N`; match the surviving terms via `ℓ = N - j`
  refine Finset.sum_bij_ne_zero (fun ij _ _ => N - ij.2) ?_ ?_ ?_ ?_
  · intro ij _ _
    exact Finset.mem_range.mpr (by omega)
  · intro ij₁ h₁ hne₁ ij₂ h₂ hne₂ heq
    have hj₁ : ij₁.2 ≤ N := by
      by_contra hcon
      apply hne₁
      simp [geometricQBinomialWeightNumerator, hcon]
    have hj₂ : ij₂.2 ≤ N := by
      by_contra hcon
      apply hne₂
      simp [geometricQBinomialWeightNumerator, hcon]
    have hm₁ := Finset.mem_antidiagonal.mp h₁
    have hm₂ := Finset.mem_antidiagonal.mp h₂
    have hjj : ij₁.2 = ij₂.2 := by omega
    exact Prod.ext (by omega) hjj
  · intro ℓ hℓ hne
    have hℓN : ℓ ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    have hnonneg : 0 ≤ (ℓ : ℤ) + ((m : ℤ) - N) := by
      by_contra hcon
      rw [not_le] at hcon
      apply hne
      rw [gaussianBinomialInt_eq_zero_of_neg q N hcon]
      ring
    have hle : (ℓ : ℤ) + ((m : ℤ) - N) ≤ N := by
      by_contra hcon
      rw [not_le] at hcon
      apply hne
      rw [gaussianBinomialInt_eq_zero_of_lt q N hcon]
      ring
    refine ⟨(((ℓ : ℤ) + ((m : ℤ) - N)).toNat, N - ℓ), ?_, ?_, ?_⟩
    · rw [Finset.mem_antidiagonal]
      show ((ℓ : ℤ) + ((m : ℤ) - N)).toNat + (N - ℓ) = m
      omega
    · rw [thetaCoeff_pair_eq q (i := ((ℓ : ℤ) + ((m : ℤ) - N)).toNat) (j := N - ℓ) (m := m)
        (by omega) (by omega) (by omega)]
      convert hne using 4 <;> simp only [Nat.sub_sub_self hℓN]
    · show N - (N - ℓ) = ℓ
      omega
  · intro ij h hne
    have hj : ij.2 ≤ N := by
      by_contra hcon
      apply hne
      simp [geometricQBinomialWeightNumerator, hcon]
    have hi : ij.1 ≤ N := by
      by_contra hcon
      rw [not_le] at hcon
      apply hne
      simp [gaussianBinomial_eq_zero_of_lt q hcon]
    exact thetaCoeff_pair_eq q hi hj (Finset.mem_antidiagonal.mp h)

/-- **The finite triple product, polynomial form.**  In every commutative
ring,
`(z;q)_N · ∏_{j<N} (z - q^{j+1}) = ∑_{m=0}^{2N} (-1)^{N+m} q^{e(m-N)} [2N, m]_q z^m`. -/
theorem finite_triple_product_poly (q z : R) (N : ℕ) :
    finiteQPochhammerIn z q N * ∏ j ∈ range N, (z - q ^ (j + 1)) =
      ∑ m ∈ range (2 * N + 1),
        (-1 : R) ^ (N + m) * q ^ thetaExponent ((m : ℤ) - N) *
          gaussianBinomial q (2 * N) m * z ^ m := by
  rw [← finite_qBinomial_theorem q z N, ← reversed_finite_qBinomial_theorem q z N]
  refine (sum_mul_sum_eq_sum_antidiagonal
    (fun i => (-1 : R) ^ i * q ^ i.choose 2 * gaussianBinomial q N i)
    (fun j => geometricQBinomialWeightNumerator q N j) N z ?_ ?_).trans ?_
  · intro i hi
    simp [gaussianBinomial_eq_zero_of_lt q hi]
  · intro j hj
    simp [geometricQBinomialWeightNumerator, not_le.mpr hj]
  · exact Finset.sum_congr rfl fun m _ => by rw [sum_antidiagonal_thetaCoeff]

end FinitePolynomial

section FiniteLaurent

variable {K : Type*} [Field K]

/-- `z^N (q/z;q)_N = ∏_{j<N} (z - q^{j+1})` for `z ≠ 0`. -/
theorem pow_mul_finiteQPochhammerIn_div (q : K) {z : K} (hz : z ≠ 0) (N : ℕ) :
    z ^ N * finiteQPochhammerIn (q / z) q N = ∏ j ∈ range N, (z - q ^ (j + 1)) := by
  unfold finiteQPochhammerIn
  have hzN : z ^ N = ∏ _j ∈ range N, z := by simp
  rw [hzN, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  field_simp
  ring

/-- `(-1)^(m - N) = (-1)^(N + m)` for integer exponents. -/
theorem neg_one_zpow_natCast_sub (m N : ℕ) :
    (-1 : K) ^ ((m : ℤ) - N) = (-1) ^ (N + m) := by
  rw [zpow_sub₀ (neg_ne_zero.mpr one_ne_zero), zpow_natCast, zpow_natCast, div_eq_mul_inv,
    ← inv_pow, inv_neg_one, ← pow_add, add_comm]

/-- **The finite triple product, Laurent form.**  For `z ≠ 0` in a field,
`(z;q)_N (q/z;q)_N = ∑_{k=-N}^{N} (-1)^k q^{e(k)} [2N, N+k]_q z^k`. -/
theorem finite_triple_product (q : K) {z : K} (hz : z ≠ 0) (N : ℕ) :
    finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        (-1 : K) ^ k * q ^ thetaExponent k * gaussianBinomialInt q (2 * N) ((N : ℤ) + k) *
          z ^ k := by
  have h := finite_triple_product_poly q z N
  rw [← pow_mul_finiteQPochhammerIn_div q hz N] at h
  apply mul_left_cancel₀ (pow_ne_zero N hz)
  rw [show z ^ N * (finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N) =
      finiteQPochhammerIn z q N * (z ^ N * finiteQPochhammerIn (q / z) q N) by ring, h,
    Finset.mul_sum]
  refine Finset.sum_nbij' (fun m => (m : ℤ) - N) (fun k => (k + N).toNat) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Icc]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro m _
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [show (N : ℤ) + ((m : ℤ) - N) = (m : ℤ) by ring, gaussianBinomialInt_ofNat,
      neg_one_zpow_natCast_sub, zpow_sub₀ hz, zpow_natCast, zpow_natCast]
    field_simp

end FiniteLaurent

/-! ## Jacobi's triple product -/

/-- The Gaussian majorant also bounds the integer-indexed coefficients. -/
theorem norm_gaussianBinomialInt_le {𝕜 : Type*} [NormedField 𝕜] {q : 𝕜} (hq : ‖q‖ < 1)
    (n : ℕ) (k : ℤ) :
    ‖gaussianBinomialInt q n k‖ ≤ gaussianMajorant q := by
  cases k with
  | ofNat k => exact norm_gaussianBinomial_le hq n k
  | negSucc k =>
      simp only [gaussianBinomialInt, norm_zero]
      exact gaussianMajorant_nonneg hq

section Infinite

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The central limit** `[2N, N+k]_q → 1/(q;q)_∞` as `N → ∞`, for every
fixed integer shift `k`. -/
theorem tendsto_gaussianBinomialInt_central {q : 𝕜} (hq : ‖q‖ < 1) (k : ℤ) :
    Tendsto (fun N : ℕ => gaussianBinomialInt q (2 * N) ((N : ℤ) + k)) atTop
      (𝓝 (qPochhammerInfIn q q)⁻¹) := by
  have hI : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  have hlim := tendsto_finiteQPochhammerIn_qPochhammerInfIn q hq
  have hA : Tendsto (fun N : ℕ => finiteQPochhammerIn q q (2 * N)) atTop
      (𝓝 (qPochhammerInfIn q q)) :=
    hlim.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun N hN => by omega⟩)
  have hB : Tendsto (fun N : ℕ => finiteQPochhammerIn q q ((N : ℤ) + k).toNat) atTop
      (𝓝 (qPochhammerInfIn q q)) :=
    hlim.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + k.natAbs, fun N hN => by omega⟩)
  have hC : Tendsto (fun N : ℕ => finiteQPochhammerIn q q ((N : ℤ) - k).toNat) atTop
      (𝓝 (qPochhammerInfIn q q)) :=
    hlim.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + k.natAbs, fun N hN => by omega⟩)
  have h := hA.div (hB.mul hC) (mul_ne_zero hI hI)
  have hval : qPochhammerInfIn q q / (qPochhammerInfIn q q * qPochhammerInfIn q q) =
      (qPochhammerInfIn q q)⁻¹ := by
    field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop k.natAbs] with N hN
  simp only [Pi.div_apply]
  have ha : (N : ℤ) + k = ((((N : ℤ) + k).toNat : ℕ) : ℤ) :=
    (Int.toNat_of_nonneg (by omega)).symm
  rw [ha, gaussianBinomialInt_ofNat,
    gaussianBinomial_eq_div hq (show ((N : ℤ) + k).toNat ≤ 2 * N by omega)]
  congr 3
  omega

/-- The theta majorant `r^{e(k)} s^k` is summable over `ℤ` for `0 ≤ r < 1`
and `s > 0`. -/
theorem summable_pow_thetaExponent_mul_zpow {r s : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hs : 0 < s) :
    Summable fun k : ℤ => r ^ thetaExponent k * s ^ k := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have h := summable_pow_choose_two_mul_pow hr0 hr hs.le
    refine h.congr fun n => ?_
    rw [thetaExponent_natCast, zpow_natCast]
  · have h := summable_pow_choose_two_mul_pow hr0 hr (inv_nonneg.mpr hs.le)
    refine h.of_nonneg_of_le (fun n => ?_) fun n => ?_
    · exact mul_nonneg (pow_nonneg hr0 _) (zpow_nonneg hs.le _)
    · rw [thetaExponent_neg_natCast, zpow_neg, zpow_natCast, ← inv_pow]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.mpr hs.le) n)
      exact pow_le_pow_of_le_one hr0 hr.le (Nat.choose_le_choose 2 (Nat.le_succ n))

/-- **Jacobi's triple product.**  For `‖q‖ < 1` and `z ≠ 0`,
`∑_{k ∈ ℤ} (-1)^k q^{k(k-1)/2} z^k = (z;q)_∞ (q/z;q)_∞ (q;q)_∞`. -/
theorem hasSum_jacobi_triple_product {q : 𝕜} (hq : ‖q‖ < 1) {z : 𝕜} (hz : z ≠ 0) :
    HasSum (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k * z ^ k)
      (qPochhammerInfIn z q * qPochhammerInfIn (q / z) q * qPochhammerInfIn q q) := by
  have hI : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  have hgm : 0 ≤ gaussianMajorant q := gaussianMajorant_nonneg hq
  have hmain : HasSum
      (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k * (qPochhammerInfIn q q)⁻¹ * z ^ k)
      (qPochhammerInfIn z q * qPochhammerInfIn (q / z) q) := by
    refine hasSum_of_tendsto_of_dominated
      (f := fun N k => (-1 : 𝕜) ^ k * q ^ thetaExponent k *
        gaussianBinomialInt q (2 * N) ((N : ℤ) + k) * z ^ k)
      (bound := fun k => gaussianMajorant q * (‖q‖ ^ thetaExponent k * ‖z‖ ^ k))
      (S := fun N => finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N)
      ?_ ?_ ?_ ?_ ?_
    · exact (summable_pow_thetaExponent_mul_zpow (norm_nonneg q) hq
        (norm_pos_iff.mpr hz)).mul_left _
    · intro k
      exact ((tendsto_gaussianBinomialInt_central hq k).const_mul
        ((-1 : 𝕜) ^ k * q ^ thetaExponent k)).mul_const (z ^ k)
    · intro N k
      rw [norm_mul, norm_mul, norm_mul, norm_zpow, norm_zpow, norm_pow, norm_neg, norm_one,
        one_zpow, one_mul]
      have h := norm_gaussianBinomialInt_le hq (2 * N) ((N : ℤ) + k)
      calc ‖q‖ ^ thetaExponent k * ‖gaussianBinomialInt q (2 * N) ((N : ℤ) + k)‖ * ‖z‖ ^ k
          ≤ ‖q‖ ^ thetaExponent k * gaussianMajorant q * ‖z‖ ^ k := by gcongr
        _ = gaussianMajorant q * (‖q‖ ^ thetaExponent k * ‖z‖ ^ k) := by ring
    · intro N
      rw [finite_triple_product q hz N]
      refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
      rcases hk with hk | hk
      · rw [gaussianBinomialInt_eq_zero_of_neg q (2 * N) (by omega)]
        ring
      · rw [gaussianBinomialInt_eq_zero_of_lt q (2 * N) (by omega)]
        ring
    · exact (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq).mul
        (tendsto_finiteQPochhammerIn_qPochhammerInfIn (q / z) hq)
  have h := hmain.mul_right (qPochhammerInfIn q q)
  have hfun : (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k * (qPochhammerInfIn q q)⁻¹ *
      z ^ k * qPochhammerInfIn q q) = fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k * z ^ k := by
    funext k
    field_simp
  rwa [hfun] at h

/-- **Jacobi's triple product, signless form.**  For `‖q‖ < 1` and `z ≠ 0`,
`∑_{k ∈ ℤ} q^{k(k-1)/2} z^k = (-z;q)_∞ (-q/z;q)_∞ (q;q)_∞`. -/
theorem hasSum_jacobi_triple_product' {q : 𝕜} (hq : ‖q‖ < 1) {z : 𝕜} (hz : z ≠ 0) :
    HasSum (fun k : ℤ => q ^ thetaExponent k * z ^ k)
      (qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q) := by
  have h := hasSum_jacobi_triple_product hq (neg_ne_zero.mpr hz)
  rw [div_neg] at h
  refine h.congr_fun ?_
  intro k
  rw [neg_eq_neg_one_mul z, mul_zpow, show (-1 : 𝕜) ^ k * q ^ thetaExponent k *
      ((-1) ^ k * z ^ k) = ((-1) ^ k * (-1) ^ k) * (q ^ thetaExponent k * z ^ k) by ring,
    ← zpow_add₀ (neg_ne_zero.mpr one_ne_zero), Even.neg_one_zpow ⟨k, rfl⟩, one_mul]

/-! ## Euler's pentagonal number theorem -/

/-- The pentagonal exponent `k(3k-1)/2 ∈ ℕ`, for every integer `k`. -/
def pentagonalExponent (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

/-- `k(3k-1) ≥ 0` for every integer `k`. -/
theorem mul_three_mul_sub_one_nonneg (k : ℤ) : 0 ≤ k * (3 * k - 1) := by
  rcases le_or_gt 1 k with h | h
  · exact mul_nonneg (by omega) (by omega)
  · have h0 : k ≤ 0 := by omega
    nlinarith

/-- `k(3k-1)` is even. -/
theorem two_dvd_mul_three_mul_sub_one (k : ℤ) : (2 : ℤ) ∣ k * (3 * k - 1) := by
  have h := two_dvd_mul_sub_one k
  have : k * (3 * k - 1) = 3 * (k * (k - 1)) + 2 * k := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right h 3) (dvd_mul_right 2 k)

/-- The defining property of the pentagonal exponent: `2 p(k) = k(3k-1)`. -/
theorem two_mul_pentagonalExponent (k : ℤ) :
    (2 : ℤ) * (pentagonalExponent k : ℤ) = k * (3 * k - 1) := by
  unfold pentagonalExponent
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg (mul_three_mul_sub_one_nonneg k) (by norm_num))]
  exact Int.mul_ediv_cancel' (two_dvd_mul_three_mul_sub_one k)

/-- `p(k) = 3 e(k) + k`. -/
theorem pentagonalExponent_eq (k : ℤ) :
    (pentagonalExponent k : ℤ) = 3 * (thetaExponent k : ℤ) + k := by
  have h1 := two_mul_pentagonalExponent k
  have h2 := two_mul_thetaExponent k
  have : (2 : ℤ) * (pentagonalExponent k : ℤ) = 2 * (3 * (thetaExponent k : ℤ) + k) := by
    linear_combination h1 - 3 * h2
  exact mul_left_cancel₀ (two_ne_zero' ℤ) this

/-- The pentagonal exponent vanishes only at `k = 0`. -/
theorem pentagonalExponent_pos {k : ℤ} (hk : k ≠ 0) : 0 < pentagonalExponent k := by
  have h := two_mul_pentagonalExponent k
  have : 0 < k * (3 * k - 1) := by
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · nlinarith
    · nlinarith
  omega

/-- **Euler's pentagonal number theorem.**  For `‖q‖ < 1`,
`(q;q)_∞ = ∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`: Jacobi's triple product at the
base `q³` and the argument `z = q`, the product side collapsing by dissection
modulo three. -/
theorem hasSum_pentagonal {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ pentagonalExponent k) (qPochhammerInfIn q q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have h : (fun k : ℤ => (-1 : 𝕜) ^ k * (0 : 𝕜) ^ pentagonalExponent k) =
        fun k : ℤ => if k = 0 then (1 : 𝕜) else 0 := by
      funext k
      split_ifs with hk
      · subst hk
        simp [pentagonalExponent]
      · rw [zero_pow (pentagonalExponent_pos hk).ne', mul_zero]
    rw [h, qPochhammerInfIn_zero_left]
    exact hasSum_ite_eq 0 1
  · have hq3 : ‖q ^ 3‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
    have h := hasSum_jacobi_triple_product hq3 hq0
    have hprod : qPochhammerInfIn q (q ^ 3) * qPochhammerInfIn (q ^ 3 / q) (q ^ 3) *
        qPochhammerInfIn (q ^ 3) (q ^ 3) = qPochhammerInfIn q q := by
      have h3 : q ^ 3 / q = q ^ 2 := by
        rw [div_eq_iff hq0]
        ring
      have e1 : q * q = q ^ 2 := by ring
      have e2 : q * q ^ 2 = q ^ 3 := by ring
      rw [h3, qPochhammerInfIn_dissection q hq (show 0 < 3 by norm_num),
        Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_zero, one_mul, pow_zero, mul_one, pow_one, e1, e2]
    rw [hprod] at h
    refine h.congr_fun fun k => ?_
    have hexp : q ^ pentagonalExponent k = (q ^ 3) ^ thetaExponent k * q ^ k := by
      rw [← pow_mul, ← zpow_natCast q (3 * thetaExponent k),
        ← zpow_natCast q (pentagonalExponent k), ← zpow_add₀ hq0]
      congr 1
      have := pentagonalExponent_eq k
      push_cast
      omega
    rw [hexp, mul_assoc]

/-- **The pentagonal number theorem, paired form.**  Pairing the terms `n`
and `-n` for `n ≥ 1`,
`(q;q)_∞ = 1 + ∑_{n≥1} (-1)^n (q^{n(3n-1)/2} + q^{n(3n+1)/2})`, since
`p(-n) = n(3n+1)/2`. -/
theorem hasSum_pentagonal_pairs {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (-1 : 𝕜) ^ (n + 1) *
        (q ^ pentagonalExponent ((n : ℤ) + 1) + q ^ pentagonalExponent (-((n : ℤ) + 1))))
      (qPochhammerInfIn q q - 1) := by
  set f : ℤ → 𝕜 := fun k => (-1 : 𝕜) ^ k * q ^ pentagonalExponent k with hf
  have h : HasSum f (qPochhammerInfIn q q) := hasSum_pentagonal hq
  obtain ⟨hpos, hneg⟩ := summable_int_iff_summable_nat_and_neg.mp h.summable
  have hneg' : Summable fun n : ℕ => f (-((n : ℤ) + 1)) := by
    have := (summable_nat_add_iff 1).mpr hneg
    refine this.congr fun n => ?_
    simp only [Nat.cast_add, Nat.cast_one]
  have hsplit : (∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1)) = qPochhammerInfIn q q := by
    rw [← h.tsum_eq, tsum_of_nat_of_neg_add_one hpos hneg']
  have hA : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) ((∑' n : ℕ, f n) - f 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hpos.hasSum
    simp only [Finset.sum_range_one, Nat.cast_zero] at this
    refine this.congr_fun fun n => ?_
    simp only [Nat.cast_add, Nat.cast_one]
  have hB : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) (∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    hneg'.hasSum
  have hf0 : f 0 = 1 := by simp [hf, pentagonalExponent]
  have hsum := hA.add hB
  rw [hf0, show (∑' n : ℕ, f n) - 1 + ∑' n : ℕ, f (-((n : ℤ) + 1)) =
    qPochhammerInfIn q q - 1 by rw [← hsplit]; ring] at hsum
  refine hsum.congr_fun fun n => ?_
  simp only [hf]
  have hz : ((-1 : 𝕜) ^ ((n : ℤ) + 1)) = (-1) ^ (n + 1) := by
    rw [← zpow_natCast]
    norm_cast
  rw [zpow_neg, ← inv_zpow, inv_neg_one, hz]
  ring

end Infinite

end

end Fabius
