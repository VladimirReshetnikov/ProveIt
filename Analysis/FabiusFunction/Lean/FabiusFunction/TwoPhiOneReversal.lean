import FabiusFunction.QPfaffSaalschutz
import FabiusFunction.GaussianBinomialInteger
import FabiusFunction.HeineTransformation

/-!
# Reversal of a terminating `₂φ₁`

For `i ≤ n` a finite `q`-shifted factorial reverses as

`(x;q)_{n-i} · (-x q^{n-i})^i q^{C(i,2)} (q^{1-n}/x; q)_i = (x;q)_n`

(`finiteQPochhammerIn_sub_eq`), since `(x;q)_n = (x;q)_{n-i} (x q^{n-i};q)_i` and the last
factor reverses base and step.  Reading the terminating sum

`₂φ₁(q^{-n}, a; c; q, z) = ∑_{j=0}^n (q^{-n};q)_j (a;q)_j / ((q;q)_j (c;q)_j) z^j`

backwards (`j = n - i`) and applying the reversal to its four symbols gives

`₂φ₁(q^{-n}, a; c; q, z) = (-1)^n q^{-C(n+1,2)} z^n (a;q)_n/(c;q)_n ·
  ₂φ₁(q^{-n}, q^{1-n}/c; q^{1-n}/a; q, c q^{n+1}/(a z))`,

an identity of rational functions in any field with `q ≠ 0`, `(q;q)_n ≠ 0`, `(c;q)_n ≠ 0` and
`(q^{1-n}/a;q)_n ≠ 0` (the last is equivalent to `(a;q)_n ≠ 0`).

## Main declarations

* `finiteQPochhammerIn_sub_eq`, `finiteQPochhammerIn_reversal_ne_zero`.
* `finiteQPochhammerIn_inv_pow_self`: `(q^{-n};q)_n = (-1)^n q^{-C(n+1,2)} (q;q)_n`.
* `twoPhiOneFinite`, `twoPhiOneFinite_reversal`, `twoPhiOneFinite_eq_sum_twoPhiOneTerm`.
* `twoPhiOneReflection`, `twoPhiOneReflection_involutive`: the reflected parameter map and its
  involutivity on nonzero parameters.
* `twoPhiOneFinite_reversal_twice`: applying the finite reversal twice, including both
  prefactors, recovers the original sum.
* `twoPhiOne_eq_twoPhiOneFinite_inv_pow`, `twoPhiOne_one_eq_twoPhiOneFinite_zero`: the
  terminating finite sum is the actual `₂φ₁` tsum, including the `n = 0`, `q = 0` boundary.
* `twoPhiOne_reversal`, `twoPhiOne_reversal_twice`: reversal and its double application for the
  actual tsum.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `C(n,2) + C(n+1,2) = n²`. -/
theorem choose_two_add_succ_choose_two (n : ℕ) : n.choose 2 + (n + 1).choose 2 = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have h2 : (n + 1 + 1).choose 2 = (n + 1) + (n + 1).choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [h1] at ih
    rw [h2, h1]
    nlinarith [ih]

variable {K : Type*} [Field K]

/-- **Reversal of a finite symbol**: for `i ≤ n`,
`(x;q)_{n-i} · (-x q^{n-i})^i q^{C(i,2)} (q^{1-n}/x; q)_i = (x;q)_n`, with `q^{1-n} = q (q^n)⁻¹`. -/
theorem finiteQPochhammerIn_sub_eq {q : K} (hq : q ≠ 0) {x : K} (hx : x ≠ 0) {i n : ℕ}
    (hi : i ≤ n) :
    finiteQPochhammerIn x q (n - i) * ((-(x * q ^ (n - i))) ^ i * q ^ i.choose 2 *
      finiteQPochhammerIn (q * (q ^ n)⁻¹ / x) q i) = finiteQPochhammerIn x q n := by
  have key : finiteQPochhammerIn (x * q ^ (n - i)) q i =
      (-(x * q ^ (n - i))) ^ i * q ^ i.choose 2 *
        finiteQPochhammerIn (q * (q ^ n)⁻¹ / x) q i := by
    rw [finiteQPochhammerIn_base_reversal (x * q ^ (n - i)) q
      (mul_ne_zero hx (pow_ne_zero _ hq)) hq, finiteQPochhammerIn_inv_base_eq hq]
    rcases i with _ | i
    · simp
    · congr 2
      obtain ⟨d, rfl⟩ : ∃ d, n = d + (i + 1) := ⟨n - (i + 1), (Nat.sub_add_cancel hi).symm⟩
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, inv_pow, pow_add, pow_succ]
      have hd : q ^ d ≠ 0 := pow_ne_zero _ hq
      have hi' : q ^ i ≠ 0 := pow_ne_zero _ hq
      field_simp
  have h := finiteQPochhammerIn_add x q (n - i) i
  rw [Nat.sub_add_cancel hi] at h
  rw [h, key]

/-- If `(x;q)_n ≠ 0` and `i ≤ n`, then `(q^{1-n}/x; q)_i ≠ 0`. -/
theorem finiteQPochhammerIn_reversal_ne_zero {q : K} (hq : q ≠ 0) {x : K} (hx : x ≠ 0)
    {i n : ℕ} (hi : i ≤ n) (hn : finiteQPochhammerIn x q n ≠ 0) :
    finiteQPochhammerIn (q * (q ^ n)⁻¹ / x) q i ≠ 0 := by
  intro h
  apply hn
  rw [← finiteQPochhammerIn_sub_eq hq hx hi, h, mul_zero, mul_zero]

/-- `(q^{-n};q)_n = (-1)^n q^{-C(n+1,2)} (q;q)_n`. -/
theorem finiteQPochhammerIn_inv_pow_self {q : K} (hq : q ≠ 0) (n : ℕ) :
    finiteQPochhammerIn (q ^ n)⁻¹ q n =
      (-1) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * finiteQPochhammerIn q q n := by
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have h := finiteQPochhammerIn_sub_eq hq (inv_ne_zero hqn) (le_refl n)
  have hbase : q * (q ^ n)⁻¹ / (q ^ n)⁻¹ = q := by
    rw [div_inv_eq_mul, mul_assoc, inv_mul_cancel₀ hqn, mul_one]
  rw [Nat.sub_self, finiteQPochhammerIn_zero, one_mul, pow_zero, mul_one, hbase] at h
  have hexp : (q ^ n) ^ n = q ^ n.choose 2 * q ^ ((n + 1).choose 2) := by
    rw [← pow_add, choose_two_add_succ_choose_two, pow_mul]
  rw [← h, neg_pow, inv_pow, hexp]
  have h1 : q ^ n.choose 2 ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ ((n + 1).choose 2) ≠ 0 := pow_ne_zero _ hq
  field_simp

/-- **The terminating `₂φ₁` sum** `∑_{j=0}^n (a;q)_j (b;q)_j / ((q;q)_j (c;q)_j) z^j`. -/
noncomputable def twoPhiOneFinite (a b c q z : K) (n : ℕ) : K :=
  ∑ j ∈ range (n + 1), finiteQPochhammerIn a q j * finiteQPochhammerIn b q j /
    (finiteQPochhammerIn q q j * finiteQPochhammerIn c q j) * z ^ j

/-- The parameter reflection in the terminating `₂φ₁` reversal:
`(a,c,z) ↦ (q^{1-n}/c, q^{1-n}/a, c q^{n+1}/(a z))`, where
`q^{1-n}` is represented by `q * (q^n)⁻¹`.

The nested product stores the parameters as `(a, (c, z))`. -/
def twoPhiOneReflection (q : K) (n : ℕ) (p : K × (K × K)) : K × (K × K) :=
  (q * (q ^ n)⁻¹ / p.2.1,
    (q * (q ^ n)⁻¹ / p.1, p.2.1 * q ^ (n + 1) / (p.1 * p.2.2)))

/-- The reflected `(a,c,z)` substitution is an involution when `q`, `a`, `c`, and `z` are
nonzero.  These are exactly the scalar nonvanishing assumptions in the reversal formula. -/
theorem twoPhiOneReflection_involutive {q : K} (hq : q ≠ 0) {a c z : K} (ha : a ≠ 0)
    (hc : c ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    twoPhiOneReflection q n (twoPhiOneReflection q n (a, (c, z))) = (a, (c, z)) := by
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hqn1 : q ^ (n + 1) ≠ 0 := pow_ne_zero _ hq
  have hs : q * (q ^ n)⁻¹ ≠ 0 := mul_ne_zero hq (inv_ne_zero hqn)
  apply Prod.ext
  · simp only [twoPhiOneReflection]
    field_simp [hs, ha, hc, hz, hqn, hqn1]
  · apply Prod.ext
    · simp only [twoPhiOneReflection]
      field_simp [hs, ha, hc, hz, hqn, hqn1]
    · simp only [twoPhiOneReflection]
      field_simp [hs, ha, hc, hz, hqn, hqn1]

set_option maxRecDepth 16384 in
/-- **Reversal of a terminating `₂φ₁`**: for `q ≠ 0`, nonzero `a, c, z`, `(q;q)_n ≠ 0`,
`(c;q)_n ≠ 0` and `(q^{1-n}/a;q)_n ≠ 0`,

`₂φ₁(q^{-n}, a; c; q, z) = (-1)^n q^{-C(n+1,2)} z^n (a;q)_n/(c;q)_n ·
  ₂φ₁(q^{-n}, q^{1-n}/c; q^{1-n}/a; q, c q^{n+1}/(a z))`,

with `q^{-n} = (q^n)⁻¹` and `q^{1-n} = q (q^n)⁻¹`. -/
theorem twoPhiOneFinite_reversal {q : K} (hq : q ≠ 0) {a c z : K} (ha : a ≠ 0) (hc : c ≠ 0)
    (hz : z ≠ 0) {n : ℕ} (hqq : finiteQPochhammerIn q q n ≠ 0)
    (hcn : finiteQPochhammerIn c q n ≠ 0)
    (han : finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q n ≠ 0) :
    twoPhiOneFinite (q ^ n)⁻¹ a c q z n =
      (-1) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * z ^ n *
        (finiteQPochhammerIn a q n / finiteQPochhammerIn c q n) *
        twoPhiOneFinite (q ^ n)⁻¹ (q * (q ^ n)⁻¹ / c) (q * (q ^ n)⁻¹ / a) q
          (c * q ^ (n + 1) / (a * z)) n := by
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hN : (q ^ n)⁻¹ ≠ 0 := inv_ne_zero hqn
  -- `(a;q)_n ≠ 0` from the hypothesis on `(q^{1-n}/a;q)_n`.
  have han' : finiteQPochhammerIn a q n ≠ 0 := by
    intro h0
    have h := finiteQPochhammerIn_sub_eq hq ha (le_refl n)
    rw [Nat.sub_self, finiteQPochhammerIn_zero, one_mul, pow_zero, mul_one, h0] at h
    rcases mul_eq_zero.mp h with h | h
    · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha)) (pow_ne_zero _ hq) h
    · exact han h
  have hNn : finiteQPochhammerIn (q ^ n)⁻¹ q n ≠ 0 := by
    rw [finiteQPochhammerIn_inv_pow_self hq]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (inv_ne_zero (pow_ne_zero _ hq))) hqq
  have hbase1 : q * (q ^ n)⁻¹ / (q ^ n)⁻¹ = q := by
    rw [div_inv_eq_mul, mul_assoc, inv_mul_cancel₀ hqn, mul_one]
  have hbase2 : q * (q ^ n)⁻¹ / q = (q ^ n)⁻¹ := mul_div_cancel_left₀ _ hq
  unfold twoPhiOneFinite
  conv_lhs => rw [← sum_range_reflect _ (n + 1)]
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp hi
  simp only [Nat.add_sub_cancel]
  -- nonvanishing of the four reversed symbols
  have hAi : finiteQPochhammerIn (q ^ n)⁻¹ q i ≠ 0 := by
    have := finiteQPochhammerIn_reversal_ne_zero hq hq hi' hqq
    rwa [hbase2] at this
  have hCi : finiteQPochhammerIn q q i ≠ 0 := by
    have := finiteQPochhammerIn_reversal_ne_zero hq hN hi' hNn
    rwa [hbase1] at this
  have hDi : finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q i ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_le _ hi' han
  have hBi : finiteQPochhammerIn (q * (q ^ n)⁻¹ / c) q i ≠ 0 :=
    finiteQPochhammerIn_reversal_ne_zero hq hc hi' hcn
  -- the four reversals in division form
  have e : ∀ x : K, x ≠ 0 → finiteQPochhammerIn (q * (q ^ n)⁻¹ / x) q i ≠ 0 →
      finiteQPochhammerIn x q (n - i) = finiteQPochhammerIn x q n /
        ((-(x * q ^ (n - i))) ^ i * q ^ i.choose 2 *
          finiteQPochhammerIn (q * (q ^ n)⁻¹ / x) q i) := fun x hx hxi =>
    eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr
      (mul_ne_zero hx (pow_ne_zero _ hq)))) (pow_ne_zero _ hq)) hxi)
      (finiteQPochhammerIn_sub_eq hq hx hi')
  rw [e (q ^ n)⁻¹ hN (by rwa [hbase1]), e a ha hDi, e q hq (by rwa [hbase2]), e c hc hBi,
    hbase1, hbase2, finiteQPochhammerIn_inv_pow_self hq]
  -- exponent bookkeeping
  have hqn' : q ^ n = q ^ (n - i) * q ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
  have hzn : z ^ n = z ^ (n - i) * z ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
  have hNQ : (q ^ n)⁻¹ * q ^ (n - i) = (q ^ i)⁻¹ := by
    rw [hqn', mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
  rw [hNQ, pow_succ, hqn', hzn, neg_pow ((q ^ i)⁻¹) i, neg_pow (a * q ^ (n - i)) i,
    neg_pow (q * q ^ (n - i)) i, neg_pow (c * q ^ (n - i)) i]
  simp only [mul_pow, div_pow, inv_pow]
  set Pa := finiteQPochhammerIn a q n with hPa
  set Pc := finiteQPochhammerIn c q n with hPc
  set Pq := finiteQPochhammerIn q q n with hPq
  set Ai := finiteQPochhammerIn (q ^ n)⁻¹ q i with hAi'
  set Bi := finiteQPochhammerIn (q * (q ^ n)⁻¹ / c) q i with hBi'
  set Ci := finiteQPochhammerIn q q i with hCi'
  set Di := finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q i with hDi'
  set Q := q ^ (n - i) with hQ
  set qi := q ^ i with hqi
  set qc := q ^ i.choose 2 with hqc
  set qC := q ^ ((n + 1).choose 2) with hqC
  set zi := z ^ i with hzi
  set zn := z ^ (n - i) with hzn'
  have hQ0 : Q ≠ 0 := pow_ne_zero _ hq
  have hqi0 : qi ≠ 0 := pow_ne_zero _ hq
  have hqc0 : qc ≠ 0 := pow_ne_zero _ hq
  have hqC0 : qC ≠ 0 := pow_ne_zero _ hq
  have hzi0 : zi ≠ 0 := pow_ne_zero _ hz
  have hzn0 : zn ≠ 0 := pow_ne_zero _ hz
  have hqii : qi ^ i ≠ 0 := pow_ne_zero _ hqi0
  field_simp

/-- Applying the terminating `₂φ₁` reversal twice returns the original finite sum.  The
second application uses exactly the reflected hypotheses supplied by the first; it introduces
no additional nonvanishing assumptions. -/
theorem twoPhiOneFinite_reversal_twice {q : K} (hq : q ≠ 0) {a c z : K} (ha : a ≠ 0)
    (hc : c ≠ 0) (hz : z ≠ 0) {n : ℕ} (hqq : finiteQPochhammerIn q q n ≠ 0)
    (hcn : finiteQPochhammerIn c q n ≠ 0)
    (han : finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q n ≠ 0) :
    let a' := q * (q ^ n)⁻¹ / c
    let c' := q * (q ^ n)⁻¹ / a
    let z' := c * q ^ (n + 1) / (a * z)
    let factor := fun x y w : K =>
      (-1) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * w ^ n *
        (finiteQPochhammerIn x q n / finiteQPochhammerIn y q n)
    factor a c z *
        (factor a' c' z' * twoPhiOneFinite (q ^ n)⁻¹ a c q z n) =
      twoPhiOneFinite (q ^ n)⁻¹ a c q z n := by
  dsimp only
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hs : q * (q ^ n)⁻¹ ≠ 0 := mul_ne_zero hq (inv_ne_zero hqn)
  have ha' : q * (q ^ n)⁻¹ / c ≠ 0 := div_ne_zero hs hc
  have hc' : q * (q ^ n)⁻¹ / a ≠ 0 := div_ne_zero hs ha
  have hz' : c * q ^ (n + 1) / (a * z) ≠ 0 :=
    div_ne_zero (mul_ne_zero hc (pow_ne_zero _ hq)) (mul_ne_zero ha hz)
  have hinv := twoPhiOneReflection_involutive hq ha hc hz n
  have hbackA : q * (q ^ n)⁻¹ / (q * (q ^ n)⁻¹ / a) = a := by
    simpa only [twoPhiOneReflection] using
      congrArg (fun p : K × (K × K) => p.1) hinv
  have hbackC : q * (q ^ n)⁻¹ / (q * (q ^ n)⁻¹ / c) = c := by
    simpa only [twoPhiOneReflection] using
      congrArg (fun p : K × (K × K) => p.2.1) hinv
  have hbackZ :
      (q * (q ^ n)⁻¹ / a) * q ^ (n + 1) /
          ((q * (q ^ n)⁻¹ / c) * (c * q ^ (n + 1) / (a * z))) = z := by
    simpa only [twoPhiOneReflection] using
      congrArg (fun p : K × (K × K) => p.2.2) hinv
  have hlast :
      finiteQPochhammerIn (q * (q ^ n)⁻¹ / (q * (q ^ n)⁻¹ / c)) q n ≠ 0 := by
    rwa [hbackC]
  have hrev1 := twoPhiOneFinite_reversal hq ha hc hz hqq hcn han
  have hrev2 := twoPhiOneFinite_reversal hq ha' hc' hz' hqq han hlast
  rw [hbackA, hbackC, hbackZ] at hrev2
  calc
    _ = (-1) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * z ^ n *
          (finiteQPochhammerIn a q n / finiteQPochhammerIn c q n) *
          twoPhiOneFinite (q ^ n)⁻¹ (q * (q ^ n)⁻¹ / c) (q * (q ^ n)⁻¹ / a) q
            (c * q ^ (n + 1) / (a * z)) n := by
      rw [← hrev2]
    _ = _ := hrev1.symm

/-- The terminating sum is the partial sum of the series `₂φ₁` of `HeineTransformation`. -/
theorem twoPhiOneFinite_eq_sum_twoPhiOneTerm {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    (a b c q z : 𝕜) (n : ℕ) : twoPhiOneFinite a b c q z n = ∑ j ∈ range (n + 1), twoPhiOneTerm a b c q z j :=
  rfl

/-- A terminating `₂φ₁` with numerator parameter `q⁻ⁿ` is exactly its finite sum.
No analytic bounds on `q` or `z`, and no denominator nonvanishing assumptions, are needed:
for every `k > n`, the numerator factor `((q^n)⁻¹;q)_k` vanishes, so the term is zero and
the defining tsum has finite support. -/
theorem twoPhiOne_eq_twoPhiOneFinite_inv_pow {𝕜 : Type*} [NormedField 𝕜]
    [CompleteSpace 𝕜] {q : 𝕜} (hq : q ≠ 0) (a c z : 𝕜) (n : ℕ) :
    twoPhiOne (q ^ n)⁻¹ a c q z = twoPhiOneFinite (q ^ n)⁻¹ a c q z n := by
  rw [twoPhiOne, twoPhiOneFinite_eq_sum_twoPhiOneTerm]
  refine tsum_eq_sum fun k hk => ?_
  rw [mem_range, not_lt] at hk
  rw [twoPhiOneTerm, finiteQPochhammerIn_inv_pow_eq_zero_of_lt q hq (by omega), zero_mul,
    zero_div, zero_mul]

/-- Reversal of a terminating `₂φ₁`, stated for the actual `twoPhiOne` tsum.  Its two
tails vanish identically, so no norm bounds or convergence hypotheses are needed. -/
theorem twoPhiOne_reversal {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {q : 𝕜} (hq : q ≠ 0) {a c z : 𝕜} (ha : a ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    {n : ℕ} (hqq : finiteQPochhammerIn q q n ≠ 0)
    (hcn : finiteQPochhammerIn c q n ≠ 0)
    (han : finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q n ≠ 0) :
    twoPhiOne (q ^ n)⁻¹ a c q z =
      (-1) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * z ^ n *
        (finiteQPochhammerIn a q n / finiteQPochhammerIn c q n) *
        twoPhiOne (q ^ n)⁻¹ (q * (q ^ n)⁻¹ / c) (q * (q ^ n)⁻¹ / a) q
          (c * q ^ (n + 1) / (a * z)) := by
  simpa only [twoPhiOne_eq_twoPhiOneFinite_inv_pow hq] using
    (twoPhiOneFinite_reversal (K := 𝕜) hq ha hc hz hqq hcn han)

/-- Applying the terminating reversal twice returns the original actual `₂φ₁` tsum,
including cancellation of the two displayed prefactors. -/
theorem twoPhiOne_reversal_twice {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {q : 𝕜} (hq : q ≠ 0) {a c z : 𝕜} (ha : a ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    {n : ℕ} (hqq : finiteQPochhammerIn q q n ≠ 0)
    (hcn : finiteQPochhammerIn c q n ≠ 0)
    (han : finiteQPochhammerIn (q * (q ^ n)⁻¹ / a) q n ≠ 0) :
    let a' := q * (q ^ n)⁻¹ / c
    let c' := q * (q ^ n)⁻¹ / a
    let z' := c * q ^ (n + 1) / (a * z)
    let factor := fun x y w : 𝕜 =>
      (-1) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * w ^ n *
        (finiteQPochhammerIn x q n / finiteQPochhammerIn y q n)
    factor a c z * (factor a' c' z' * twoPhiOne (q ^ n)⁻¹ a c q z) =
      twoPhiOne (q ^ n)⁻¹ a c q z := by
  simpa only [twoPhiOne_eq_twoPhiOneFinite_inv_pow hq] using
    (twoPhiOneFinite_reversal_twice (K := 𝕜) hq ha hc hz hqq hcn han)

/-- The `n = 0` terminating boundary does not require `q ≠ 0`: the first numerator parameter
is `1`, so `(1;q)_k = 0` for every positive `k`.  In particular this covers `q = 0`, which the
general `q⁻ⁿ` theorem above intentionally excludes. -/
theorem twoPhiOne_one_eq_twoPhiOneFinite_zero {𝕜 : Type*} [NormedField 𝕜]
    [CompleteSpace 𝕜] (a c q z : 𝕜) :
    twoPhiOne 1 a c q z = twoPhiOneFinite 1 a c q z 0 := by
  rw [twoPhiOne, twoPhiOneFinite_eq_sum_twoPhiOneTerm]
  refine tsum_eq_sum fun k hk => ?_
  rw [mem_range, not_lt] at hk
  have hkpos : 0 < k := by omega
  have hzero : finiteQPochhammerIn (1 : 𝕜) q k = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    exact finiteQPochhammerIn_one_left q j
  rw [twoPhiOneTerm, hzero, zero_mul, zero_div, zero_mul]

end Fabius
