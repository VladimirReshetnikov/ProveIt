import FabiusFunction.TwoPhiOneReversal
import FabiusFunction.QBinomialCauchy
import FabiusFunction.GaussianBinomialBounds

/-!
# The two `q`-Chu–Vandermonde sums

The first `q`-Chu–Vandermonde sum

`₂φ₁(q^{-n}, A; C; q, C q^n/A) = (C/A;q)_n / (C;q)_n`

is, after clearing `(C;q)_n`, the polynomial identity

`(C/A;q)_n = ∑_k [n,k]_q (-1)^k q^{C(k,2)} (C/A)^k (A;q)_k (C q^k;q)_{n-k}`,

and this is *exactly* the finite `q`-Cauchy identity
`(uv;q)_n = ∑_k [n,k]_q (u;q)_k v^k (v;q)_{n-k}` at base `q⁻¹` with `u = 1/A`,
`v = C q^{n-1}`: transcribing the base-`q⁻¹` symbols and Gaussian coefficients back to base `q`
(`finiteQPochhammerIn_inv_base_eq`, `finiteQPochhammerIn_inv_base_reversal`,
`gaussianBinomial_inv`) produces precisely the sign and the power `q^{C(k,2)}`, because
`k(n-1) = k(n-k) + 2·C(k,2)`.  Hence the sum holds in every field with `q ≠ 0`, `A ≠ 0`,
`(q;q)_n ≠ 0`, `(C;q)_n ≠ 0`, with no limiting process.

The second sum

`₂φ₁(q^{-n}, A; C; q, q) = A^n (C/A;q)_n / (C;q)_n`

has a direct denominator-cleared proof from the same finite `q`-Cauchy identity at base
`q⁻¹`.  After the terminating numerator and `(C;q)_n` are cleared, base reversal and
Gaussian reciprocity turn its `k`-th summand into
`[n,k]_{q⁻¹} A^k (A⁻¹;q⁻¹)_k (Cq^k;q)_{n-k}`.  Reflecting `k ↔ n-k`
gives finite `q`-Cauchy with `u = Cq^{n-1}` and `v = A⁻¹`.  This argument needs neither
`C ≠ 0` nor `(A;q)_n ≠ 0`.

## Main declarations

* `two_mul_choose_two`, `mul_sub_one_eq_mul_sub_add`: the exponent bookkeeping.
* `finiteQPochhammerIn_div_eq_sum_chu`, `finiteQPochhammerIn_div_eq_sum_chu_second`:
  the two denominator-cleared sums.
* `q_chu_vandermonde_first`, `q_chu_vandermonde_second`, and the explicit provenance
  theorem `q_chu_vandermonde_second_by_reversal`.
* `twoPhiOne_q_chu_vandermonde_first`, `twoPhiOne_q_chu_vandermonde_second`: wrappers for
  the actual `twoPhiOne` tsum.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `2·C(k,2) = k(k-1)`. -/
theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel, mul_add, ih]
    rcases k with _ | k
    · rfl
    · rw [Nat.add_sub_cancel]
      ring

/-- For `k ≤ n`: `k(n-1) = k(n-k) + 2·C(k,2)`. -/
theorem mul_sub_one_eq_mul_sub_add {k n : ℕ} (hk : k ≤ n) :
    k * (n - 1) = k * (n - k) + 2 * k.choose 2 := by
  rcases k with _ | k
  · simp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [two_mul_choose_two, show k + 1 + j - 1 = k + j by omega, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel]
  ring

variable {K : Type*} [Field K]

set_option maxRecDepth 8192 in
/-- **The cleared first `q`-Chu–Vandermonde sum**, i.e. the finite `q`-Cauchy identity at base
`q⁻¹`:
`(C/A;q)_n = ∑_k [n,k]_q (-1)^k q^{C(k,2)} (C/A)^k (A;q)_k (C q^k;q)_{n-k}`. -/
theorem finiteQPochhammerIn_div_eq_sum_chu {q : K} (hq : q ≠ 0) {A : K} (hA : A ≠ 0) (C : K)
    (n : ℕ) :
    finiteQPochhammerIn (C / A) q n =
      ∑ k ∈ range (n + 1), gaussianBinomial q n k * (-1) ^ k * q ^ k.choose 2 * (C / A) ^ k *
        finiteQPochhammerIn A q k * finiteQPochhammerIn (C * q ^ k) q (n - k) := by
  have h := finite_qCauchy_identity q⁻¹ A⁻¹ (C * q ^ (n - 1)) n
  have hL : finiteQPochhammerIn (A⁻¹ * (C * q ^ (n - 1))) q⁻¹ n =
      finiteQPochhammerIn (C / A) q n := by
    rw [finiteQPochhammerIn_inv_base_eq hq]
    congr 1
    rw [inv_pow]
    have : q ^ (n - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
  rw [hL] at h
  rw [h]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  -- the Gaussian coefficient at base `q⁻¹`
  have hG : gaussianBinomial q⁻¹ n k = gaussianBinomial q n k / q ^ (k * (n - k)) := by
    rw [gaussianBinomial_inv q hq hk', mul_div_cancel_left₀ _ (pow_ne_zero _ hq)]
  -- the first symbol at base `q⁻¹`
  have hA' : finiteQPochhammerIn A⁻¹ q⁻¹ k =
      (-A⁻¹) ^ k * (q⁻¹) ^ k.choose 2 * finiteQPochhammerIn A q k := by
    rw [finiteQPochhammerIn_inv_base_reversal A⁻¹ q (inv_ne_zero hA) hq, inv_inv]
  -- the second symbol at base `q⁻¹`
  have hS : finiteQPochhammerIn (C * q ^ (n - 1)) q⁻¹ (n - k) =
      finiteQPochhammerIn (C * q ^ k) q (n - k) := by
    rcases eq_or_lt_of_le hk' with rfl | hlt
    · simp
    · rw [finiteQPochhammerIn_inv_base_eq hq]
      congr 1
      rw [inv_pow, mul_assoc, show q ^ (n - 1) = q ^ k * q ^ (n - k - 1) by
        rw [← pow_add]; congr 1; omega]
      have : q ^ (n - k - 1) ≠ 0 := pow_ne_zero _ hq
      field_simp
  rw [hG, hA', hS]
  -- exponent bookkeeping: `(q^{n-1})^k = q^{k(n-k)} q^{C(k,2)} q^{C(k,2)}`
  have hexp : (q ^ (n - 1)) ^ k = q ^ (k * (n - k)) * q ^ k.choose 2 * q ^ k.choose 2 := by
    rw [← pow_mul, mul_comm (n - 1) k, mul_sub_one_eq_mul_sub_add hk', ← pow_add, ← pow_add,
      two_mul, add_assoc]
  rw [mul_pow, hexp, neg_pow]
  simp only [div_pow, inv_pow]
  have h1 : q ^ (k * (n - k)) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ k.choose 2 ≠ 0 := pow_ne_zero _ hq
  have h3 : A ^ k ≠ 0 := pow_ne_zero _ hA
  field_simp

/-- **The first `q`-Chu–Vandermonde sum**: for `q ≠ 0`, `A ≠ 0`, `(q;q)_n ≠ 0`, `(C;q)_n ≠ 0`,
`₂φ₁(q^{-n}, A; C; q, C q^n/A) = (C/A;q)_n / (C;q)_n`. -/
theorem q_chu_vandermonde_first {q : K} (hq : q ≠ 0) {A C : K} (hA : A ≠ 0) {n : ℕ}
    (hqq : finiteQPochhammerIn q q n ≠ 0) (hCn : finiteQPochhammerIn C q n ≠ 0) :
    twoPhiOneFinite (q ^ n)⁻¹ A C q (C * q ^ n / A) n =
      finiteQPochhammerIn (C / A) q n / finiteQPochhammerIn C q n := by
  rw [eq_div_iff hCn, finiteQPochhammerIn_div_eq_sum_chu hq hA C n, twoPhiOneFinite, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hC := finiteQPochhammerIn_add C q k (n - k)
  rw [Nat.add_sub_of_le hk'] at hC
  have hCk : finiteQPochhammerIn C q k ≠ 0 := finiteQPochhammerIn_ne_zero_of_le _ hk' hCn
  have hqk : finiteQPochhammerIn q q k ≠ 0 := finiteQPochhammerIn_ne_zero_of_le _ hk' hqq
  have hN : finiteQPochhammerIn (q ^ n)⁻¹ q k =
      (-1) ^ k * q ^ k.choose 2 * (finiteQPochhammerIn q q k * gaussianBinomial q n k) /
        q ^ (n * k) := by
    rw [finiteQPochhammerIn_self_mul_gaussianBinomial q hk',
      ← pow_mul_finiteQPochhammerIn_inv_pow_eq q hq hk',
      mul_div_cancel_left₀ _ (pow_ne_zero _ hq)]
  rw [hC, hN]
  simp only [div_pow, mul_pow]
  rw [← pow_mul]
  have hqnk : q ^ (n * k) ≠ 0 := pow_ne_zero _ hq
  have hAk : A ^ k ≠ 0 := pow_ne_zero _ hA
  field_simp

set_option maxRecDepth 8192 in
/-- **The denominator-cleared second `q`-Chu–Vandermonde sum.**  For `q ≠ 0` and
`A ≠ 0`, with no condition on `C`,

`A^n (C/A;q)_n = Σ_k [n,k]_q (-1)^k q^{C(k,2)} (A;q)_k q^k q^{-nk}
  (Cq^k;q)_{n-k}`.

The proof is finite `q`-Cauchy at base `q⁻¹`, followed by reflection of the summation
index.  It is a Laurent-polynomial identity: no `q`-Pochhammer factor is cancelled. -/
theorem finiteQPochhammerIn_div_eq_sum_chu_second {q : K} (hq : q ≠ 0) {A : K}
    (hA : A ≠ 0) (C : K) (n : ℕ) :
    A ^ n * finiteQPochhammerIn (C / A) q n =
      ∑ k ∈ range (n + 1),
        (gaussianBinomial q n k * (-1) ^ k * q ^ k.choose 2 *
          finiteQPochhammerIn A q k * q ^ k / q ^ (n * k)) *
            finiteQPochhammerIn (C * q ^ k) q (n - k) := by
  have hCauchy := finite_qCauchy_identity q⁻¹ (C * q ^ (n - 1)) A⁻¹ n
  have hleft :
      finiteQPochhammerIn ((C * q ^ (n - 1)) * A⁻¹) q⁻¹ n =
        finiteQPochhammerIn (C / A) q n := by
    calc
      finiteQPochhammerIn ((C * q ^ (n - 1)) * A⁻¹) q⁻¹ n =
          finiteQPochhammerIn ((C / A) * q ^ (n - 1)) q⁻¹ n := by
        congr 1
        simp only [div_eq_mul_inv]
        ring
      _ = finiteQPochhammerIn (C / A) q n :=
        finiteQPochhammerIn_mul_pow_inv_base hq (C / A) n
  have hsum :
      A ^ n * finiteQPochhammerIn (C / A) q n =
        ∑ k ∈ range (n + 1),
          gaussianBinomial q⁻¹ n k * A ^ k * finiteQPochhammerIn A⁻¹ q⁻¹ k *
            finiteQPochhammerIn (C * q ^ k) q (n - k) := by
    rw [← hleft, hCauchy, mul_sum]
    conv_rhs => rw [← sum_range_reflect _ (n + 1)]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hi']
    have htail :
        finiteQPochhammerIn (C * q ^ (n - 1)) q⁻¹ i =
          finiteQPochhammerIn (C * q ^ (n - i)) q i := by
      rcases i with _ | i
      · simp
      · rw [finiteQPochhammerIn_inv_base_eq hq]
        congr 1
        simp only [Nat.add_sub_cancel, inv_pow]
        rw [mul_assoc, show q ^ (n - 1) = q ^ (n - (i + 1)) * q ^ i by
          rw [← pow_add]
          congr 1
          omega]
        have hqi : q ^ i ≠ 0 := pow_ne_zero _ hq
        field_simp
    have hpow : A ^ n * (A⁻¹) ^ i = A ^ (n - i) := by
      rw [show A ^ n = A ^ (n - i) * A ^ i by
        rw [← pow_add, Nat.sub_add_cancel hi'], inv_pow, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hA), mul_one]
    rw [gaussianBinomial_symm q⁻¹ hi', ← htail, ← hpow]
    ring
  rw [hsum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hdegree :
      k.choose 2 + k.choose 2 + k * (n - k) + k = n * k := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk'
    rw [Nat.add_sub_cancel_left, ← two_mul, two_mul_choose_two]
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel]
      ring
  have hexp :
      q ^ k.choose 2 * q ^ k.choose 2 * q ^ (k * (n - k)) * q ^ k = q ^ (n * k) := by
    rw [← pow_add, ← pow_add, ← pow_add, hdegree]
  have hsign : (-1 : K) ^ k * (-1 : K) ^ k = 1 := by
    rw [← mul_pow]
    simp
  have hcoeff :
      gaussianBinomial q n k * (-1) ^ k * q ^ k.choose 2 *
          finiteQPochhammerIn A q k * q ^ k / q ^ (n * k) =
        gaussianBinomial q⁻¹ n k * A ^ k * finiteQPochhammerIn A⁻¹ q⁻¹ k := by
    rw [gaussianBinomial_inv q hq hk', finiteQPochhammerIn_base_reversal A q hA hq,
      neg_pow, div_eq_iff (pow_ne_zero _ hq), ← hexp]
    calc
      _ = ((-1 : K) ^ k * (-1 : K) ^ k) *
          (gaussianBinomial q⁻¹ n k * A ^ k * finiteQPochhammerIn A⁻¹ q⁻¹ k *
            (q ^ k.choose 2 * q ^ k.choose 2 * q ^ (k * (n - k)) * q ^ k)) := by
        ring
      _ = _ := by rw [hsign]; ring
  rw [hcoeff]

/-- The second `q`-Chu–Vandermonde identity after clearing its only parameter denominator.
Unlike the quotient wrapper, this form records explicitly that no `(A;q)_n ≠ 0` or
`C ≠ 0` assumption is involved. -/
theorem twoPhiOneFinite_mul_finiteQPochhammerIn_eq_chu_second {q : K} (hq : q ≠ 0)
    {A C : K} (hA : A ≠ 0) {n : ℕ} (hqq : finiteQPochhammerIn q q n ≠ 0)
    (hCn : finiteQPochhammerIn C q n ≠ 0) :
    twoPhiOneFinite (q ^ n)⁻¹ A C q q n * finiteQPochhammerIn C q n =
      A ^ n * finiteQPochhammerIn (C / A) q n := by
  rw [finiteQPochhammerIn_div_eq_sum_chu_second hq hA C n]
  unfold twoPhiOneFinite
  rw [sum_mul]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hC := finiteQPochhammerIn_add C q k (n - k)
  rw [Nat.add_sub_of_le hk'] at hC
  have hCk : finiteQPochhammerIn C q k ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_le _ hk' hCn
  have hqk : finiteQPochhammerIn q q k ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_le _ hk' hqq
  have hN : finiteQPochhammerIn (q ^ n)⁻¹ q k =
      (-1) ^ k * q ^ k.choose 2 * (finiteQPochhammerIn q q k * gaussianBinomial q n k) /
        q ^ (n * k) := by
    rw [finiteQPochhammerIn_self_mul_gaussianBinomial q hk',
      ← pow_mul_finiteQPochhammerIn_inv_pow_eq q hq hk',
      mul_div_cancel_left₀ _ (pow_ne_zero _ hq)]
  rw [hC, hN]
  have hqnk : q ^ (n * k) ≠ 0 := pow_ne_zero _ hq
  field_simp

/-- **The second `q`-Chu–Vandermonde sum** wherever its displayed rational expressions are
defined: for `q ≠ 0`, `A ≠ 0`, `(q;q)_n ≠ 0`, and `(C;q)_n ≠ 0`,
`₂φ₁(q^{-n}, A; C; q, q) = A^n (C/A;q)_n / (C;q)_n`.

In particular, neither `C ≠ 0` nor `(A;q)_n ≠ 0` is required. -/
theorem q_chu_vandermonde_second {q : K} (hq : q ≠ 0) {A C : K} (hA : A ≠ 0) {n : ℕ}
    (hqq : finiteQPochhammerIn q q n ≠ 0) (hCn : finiteQPochhammerIn C q n ≠ 0) :
    twoPhiOneFinite (q ^ n)⁻¹ A C q q n =
      A ^ n * finiteQPochhammerIn (C / A) q n / finiteQPochhammerIn C q n := by
  rw [eq_div_iff hCn]
  exact twoPhiOneFinite_mul_finiteQPochhammerIn_eq_chu_second hq hA hqq hCn

/-- **The second `q`-Chu–Vandermonde sum by the monograph's reversal argument.**
This theorem preserves the explicit proof provenance through `twoPhiOneFinite_reversal`.
Its additional `C ≠ 0` and `(A;q)_n ≠ 0` assumptions belong to that derivation, not to
the identity itself; `q_chu_vandermonde_second` above is the stronger full-domain theorem. -/
theorem q_chu_vandermonde_second_by_reversal {q : K} (hq : q ≠ 0) {A C : K}
    (hA : A ≠ 0) (hC : C ≠ 0) {n : ℕ} (hqq : finiteQPochhammerIn q q n ≠ 0)
    (hAn : finiteQPochhammerIn A q n ≠ 0) (hCn : finiteQPochhammerIn C q n ≠ 0) :
    twoPhiOneFinite (q ^ n)⁻¹ A C q q n =
      A ^ n * finiteQPochhammerIn (C / A) q n / finiteQPochhammerIn C q n := by
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hN : q * (q ^ n)⁻¹ ≠ 0 := mul_ne_zero hq (inv_ne_zero hqn)
  have hrevC := finiteQPochhammerIn_sub_eq hq hC (le_refl n)
  rw [Nat.sub_self, finiteQPochhammerIn_zero, one_mul, pow_zero, mul_one] at hrevC
  set a := q * (q ^ n)⁻¹ / C with ha_def
  set c := q * (q ^ n)⁻¹ / A with hc_def
  have ha : a ≠ 0 := div_ne_zero hN hC
  have hc : c ≠ 0 := div_ne_zero hN hA
  have hcn : finiteQPochhammerIn c q n ≠ 0 :=
    finiteQPochhammerIn_reversal_ne_zero hq hA le_rfl hAn
  have hra : q * (q ^ n)⁻¹ / a = C := by
    rw [ha_def]
    field_simp
  have hrc : q * (q ^ n)⁻¹ / c = A := by
    rw [hc_def]
    field_simp
  have han : finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q n ≠ 0 := by rwa [hra]
  have hz : c * q ^ n / a ≠ 0 := div_ne_zero (mul_ne_zero hc hqn) ha
  have hrev := twoPhiOneFinite_reversal hq ha hc hz hqq hcn han
  have hzq : c * q ^ (n + 1) / (a * (c * q ^ n / a)) = q := by
    field_simp
    ring
  rw [hra, hrc, hzq, q_chu_vandermonde_first hq ha hqq hcn] at hrev
  have hca : c / a = C / A := by
    rw [ha_def, hc_def]
    field_simp
  have hcza : c * q ^ n / a = C * q ^ n / A := by
    rw [ha_def, hc_def]
    field_simp
  rw [hca, hcza] at hrev
  have hrev' := (div_eq_iff hcn).mp hrev
  rw [eq_div_iff hCn, ← hrevC, hrev']
  have hqexp : (q ^ n) ^ n = q ^ n.choose 2 * q ^ ((n + 1).choose 2) := by
    rw [← pow_add, choose_two_add_succ_choose_two, pow_mul]
  simp only [div_pow, mul_pow]
  rw [hqexp]
  have h1 : q ^ n.choose 2 ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ ((n + 1).choose 2) ≠ 0 := pow_ne_zero _ hq
  have h3 : A ^ n ≠ 0 := pow_ne_zero _ hA
  have h4 : finiteQPochhammerIn a q n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrevC
    exact hCn hrevC.symm
  field_simp
  rw [neg_pow]
  ring

/-- The first terminating `q`-Chu–Vandermonde sum, stated for the actual `twoPhiOne` tsum. -/
theorem twoPhiOne_q_chu_vandermonde_first {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {q : 𝕜} (hq : q ≠ 0) {A C : 𝕜} (hA : A ≠ 0) {n : ℕ}
    (hqq : finiteQPochhammerIn q q n ≠ 0) (hCn : finiteQPochhammerIn C q n ≠ 0) :
    twoPhiOne (q ^ n)⁻¹ A C q (C * q ^ n / A) =
      finiteQPochhammerIn (C / A) q n / finiteQPochhammerIn C q n := by
  simpa only [twoPhiOne_eq_twoPhiOneFinite_inv_pow hq] using
    (q_chu_vandermonde_first (K := 𝕜) hq hA hqq hCn)

/-- The full-domain second terminating `q`-Chu–Vandermonde sum, stated for the actual
`twoPhiOne` tsum. -/
theorem twoPhiOne_q_chu_vandermonde_second {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {q : 𝕜} (hq : q ≠ 0) {A C : 𝕜} (hA : A ≠ 0) {n : ℕ}
    (hqq : finiteQPochhammerIn q q n ≠ 0) (hCn : finiteQPochhammerIn C q n ≠ 0) :
    twoPhiOne (q ^ n)⁻¹ A C q q =
      A ^ n * finiteQPochhammerIn (C / A) q n / finiteQPochhammerIn C q n := by
  simpa only [twoPhiOne_eq_twoPhiOneFinite_inv_pow hq] using
    (q_chu_vandermonde_second (K := 𝕜) hq hA hqq hCn)

end Fabius
