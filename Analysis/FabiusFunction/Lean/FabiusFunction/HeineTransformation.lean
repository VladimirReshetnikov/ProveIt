import FabiusFunction.QPochhammerInfiniteBounds

/-!
# The basic hypergeometric series ₂φ₁ and Heine's transformation

`₂φ₁(a,b;c;q,z) = ∑_{n≥0} (a;q)_n (b;q)_n / ((q;q)_n (c;q)_n) z^n` converges
absolutely for `‖q‖ < 1`, `‖z‖ < 1` and `(c;q)_∞ ≠ 0` (no `c q^j = 1`), by the
uniform bounds of `QPochhammerInfiniteBounds`.

**Heine's transformation** reads, for `‖b‖ < 1`, `b ≠ 0`, `‖z‖ < 1`, and
nonvanishing `(c;q)_∞`, `(az;q)_∞`:

`₂φ₁(a,b;c;q,z) = (b;q)_∞ (az;q)_∞ / ((c;q)_∞ (z;q)_∞) · ₂φ₁(c/b, z; az; q, b)`.

The proof is the classical one.  The ratio `(b;q)_n/(c;q)_n` is
`(b;q)_∞/(c;q)_∞ · (cq^n;q)_∞/(bq^n;q)_∞`, and the last quotient is the
`q`-binomial series `∑_k (c/b;q)_k/(q;q)_k (bq^n)^k`; inserting it gives a
double series `∑_{n,k} F(n,k)` dominated by `∑ ‖z‖^n ‖b‖^k`, whose order of
summation may therefore be exchanged; summing over `n` first is again the
`q`-binomial theorem at `zq^k`, and `(azq^k;q)_∞/(zq^k;q)_∞` is
`(az;q)_∞/(z;q)_∞ · (z;q)_k/(az;q)_k`.

## Main declarations

* `twoPhiOneTerm`, `twoPhiOne`: the terms and the sum of `₂φ₁`.
* `summable_twoPhiOneTerm`, `hasSum_twoPhiOne`: absolute convergence in the
  unit disc.
* `heine_transformation`: Heine's transformation.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- The `n`-th term `(a;q)_n (b;q)_n / ((q;q)_n (c;q)_n) z^n` of `₂φ₁(a,b;c;q,z)`. -/
noncomputable def twoPhiOneTerm (a b c q z : 𝕜) (n : ℕ) : 𝕜 :=
  finiteQPochhammerIn a q n * finiteQPochhammerIn b q n /
    (finiteQPochhammerIn q q n * finiteQPochhammerIn c q n) * z ^ n

/-- The basic hypergeometric series `₂φ₁(a,b;c;q,z)`. -/
noncomputable def twoPhiOne (a b c q z : 𝕜) : 𝕜 := ∑' n : ℕ, twoPhiOneTerm a b c q z n

/-- The terms of `₂φ₁` are dominated by a geometric series. -/
theorem exists_norm_twoPhiOneTerm_le (a b : 𝕜) {c q : 𝕜} (hq : ‖q‖ < 1)
    (hc : qPochhammerInfIn c q ≠ 0) (z : 𝕜) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖twoPhiOneTerm a b c q z n‖ ≤ K * ‖z‖ ^ n := by
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    exists_norm_finiteQPochhammerIn_div_le a hq (qPochhammerInfIn_self_ne_zero hq)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_finiteQPochhammerIn_div_le b hq hc
  refine ⟨K₁ * K₂, mul_nonneg hK₁0 hK₂0, fun n => ?_⟩
  have h : twoPhiOneTerm a b c q z n =
      finiteQPochhammerIn a q n / finiteQPochhammerIn q q n *
        (finiteQPochhammerIn b q n / finiteQPochhammerIn c q n) * z ^ n := by
    rw [twoPhiOneTerm]
    ring
  rw [h, norm_mul, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hK₁ n) (hK₂ n) (norm_nonneg _) hK₁0)
    (pow_nonneg (norm_nonneg z) n)

/-- **Absolute convergence** of `₂φ₁(a,b;c;q,z)` for `‖q‖ < 1`, `‖z‖ < 1`, `(c;q)_∞ ≠ 0`. -/
theorem summable_twoPhiOneTerm (a b : 𝕜) {c q : 𝕜} (hq : ‖q‖ < 1)
    (hc : qPochhammerInfIn c q ≠ 0) {z : 𝕜} (hz : ‖z‖ < 1) :
    Summable (twoPhiOneTerm a b c q z) := by
  obtain ⟨K, _, hK⟩ := exists_norm_twoPhiOneTerm_le a b hq hc z
  exact ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left K).of_norm_bounded hK

/-- The defining terms sum to `twoPhiOne` throughout its open unit disc of
absolute convergence. -/
theorem hasSum_twoPhiOne (a b : 𝕜) {c q : 𝕜} (hq : ‖q‖ < 1)
    (hc : qPochhammerInfIn c q ≠ 0) {z : 𝕜} (hz : ‖z‖ < 1) :
    HasSum (twoPhiOneTerm a b c q z) (twoPhiOne a b c q z) :=
  (summable_twoPhiOneTerm a b hq hc hz).hasSum

/-- Shifting the parameter by `q^n` divides the infinite product by the prefix. -/
theorem qPochhammerInfIn_mul_pow_div (a : 𝕜) {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ)
    (hn : finiteQPochhammerIn a q n ≠ 0) :
    qPochhammerInfIn (a * q ^ n) q = qPochhammerInfIn a q / finiteQPochhammerIn a q n := by
  rw [qPochhammerInfIn_eq_finite_mul_shift a hq n, mul_div_cancel_left₀ _ hn]

/-- **Heine's transformation.**  For `‖q‖ < 1`, `‖b‖ < 1`, `b ≠ 0`, `‖z‖ < 1`,
and nonvanishing `(c;q)_∞` and `(az;q)_∞`,
`₂φ₁(a,b;c;q,z) = (b;q)_∞ (az;q)_∞ / ((c;q)_∞ (z;q)_∞) · ₂φ₁(c/b, z; az; q, b)`. -/
theorem heine_transformation {q : 𝕜} (hq : ‖q‖ < 1) (a : 𝕜) {b : 𝕜} (hb0 : b ≠ 0)
    (hb : ‖b‖ < 1) {c : 𝕜} (hc : qPochhammerInfIn c q ≠ 0) {z : 𝕜} (hz : ‖z‖ < 1)
    (haz : qPochhammerInfIn (a * z) q ≠ 0) :
    twoPhiOne a b c q z =
      qPochhammerInfIn b q * qPochhammerInfIn (a * z) q /
        (qPochhammerInfIn c q * qPochhammerInfIn z q) * twoPhiOne (c / b) z (a * z) q b := by
  -- the two coefficient sequences and the double series
  obtain ⟨A, hA⟩ : ∃ A : ℕ → 𝕜,
      ∀ n, A n = finiteQPochhammerIn a q n / finiteQPochhammerIn q q n := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → 𝕜,
      ∀ k, B k = finiteQPochhammerIn (c / b) q k / finiteQPochhammerIn q q k :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ × ℕ → 𝕜,
      ∀ p : ℕ × ℕ, F p = A p.1 * z ^ p.1 * (B p.2 * b ^ p.2) * q ^ (p.1 * p.2) :=
    ⟨_, fun _ => rfl⟩
  -- nonvanishing facts
  have hbinf : qPochhammerInfIn b q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hb
  have hzinf : qPochhammerInfIn z q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz
  have hbn : ∀ n, finiteQPochhammerIn b q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_norm_lt_one hq hb
  have hzn : ∀ n, finiteQPochhammerIn z q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_norm_lt_one hq hz
  have hcn : ∀ n, finiteQPochhammerIn c q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero c hq hc
  have hazn : ∀ n, finiteQPochhammerIn (a * z) q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (a * z) hq haz
  have hbq : ∀ n : ℕ, ‖b * q ^ n‖ < 1 := fun n => by
    rw [norm_mul, norm_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg b)
      (pow_le_one₀ (norm_nonneg q) hq.le)) hb
  have hzq : ∀ k : ℕ, ‖z * q ^ k‖ < 1 := fun k => by
    rw [norm_mul, norm_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg z)
      (pow_le_one₀ (norm_nonneg q) hq.le)) hz
  -- absolute convergence of the double series
  obtain ⟨KA, hKA0, hKA⟩ :=
    exists_norm_finiteQPochhammerIn_div_le a hq (qPochhammerInfIn_self_ne_zero hq)
  obtain ⟨KB, hKB0, hKB⟩ :=
    exists_norm_finiteQPochhammerIn_div_le (c / b) hq (qPochhammerInfIn_self_ne_zero hq)
  have hFle : ∀ p : ℕ × ℕ, ‖F p‖ ≤ KA * KB * (‖z‖ ^ p.1 * ‖b‖ ^ p.2) := by
    rintro ⟨n, k⟩
    rw [hF]
    simp only [norm_mul, norm_pow]
    have h1 : ‖q‖ ^ (n * k) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
    have hAn : ‖A n‖ ≤ KA := by rw [hA]; exact hKA n
    have hBk : ‖B k‖ ≤ KB := by rw [hB]; exact hKB k
    calc ‖A n‖ * ‖z‖ ^ n * (‖B k‖ * ‖b‖ ^ k) * ‖q‖ ^ (n * k)
        ≤ ‖A n‖ * ‖z‖ ^ n * (‖B k‖ * ‖b‖ ^ k) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖A n‖ * ‖B k‖ * (‖z‖ ^ n * ‖b‖ ^ k) := by ring
      _ ≤ KA * KB * (‖z‖ ^ n * ‖b‖ ^ k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hAn hBk (norm_nonneg _) hKA0) (by positivity)
  have hgeom : Summable fun p : ℕ × ℕ => KA * KB * (‖z‖ ^ p.1 * ‖b‖ ^ p.2) :=
    (Summable.mul_of_nonneg (f := fun n : ℕ => ‖z‖ ^ n) (g := fun k : ℕ => ‖b‖ ^ k)
      (summable_geometric_of_lt_one (norm_nonneg z) hz)
      (summable_geometric_of_lt_one (norm_nonneg b) hb) (fun n => pow_nonneg (norm_nonneg z) n)
      (fun k => pow_nonneg (norm_nonneg b) k)).mul_left (KA * KB)
  have hFsum : Summable F := hgeom.of_norm_bounded hFle
  -- rows: for fixed `n`, sum over `k` by the `q`-binomial theorem at `b q^n`
  have hrow : ∀ n : ℕ, HasSum (fun k => F (n, k))
      (qPochhammerInfIn c q / qPochhammerInfIn b q * twoPhiOneTerm a b c q z n) := by
    intro n
    have h := (hasSum_qBinomial_theorem hq (c / b) (hbq n)).mul_left (A n * z ^ n)
    have hcb : c / b * (b * q ^ n) = c * q ^ n := by
      rw [div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hb0]
    rw [hcb, qPochhammerInfIn_mul_pow_div c hq n (hcn n),
      qPochhammerInfIn_mul_pow_div b hq n (hbn n)] at h
    have hval : A n * z ^ n * (qPochhammerInfIn c q / finiteQPochhammerIn c q n /
        (qPochhammerInfIn b q / finiteQPochhammerIn b q n)) =
        qPochhammerInfIn c q / qPochhammerInfIn b q * twoPhiOneTerm a b c q z n := by
      rw [hA, twoPhiOneTerm, div_div_div_eq]
      ring
    rw [hval] at h
    refine h.congr_fun fun k => ?_
    rw [hF, hB, mul_pow, ← pow_mul]
    ring
  -- columns: for fixed `k`, sum over `n` by the `q`-binomial theorem at `z q^k`
  have hcol : ∀ k : ℕ, HasSum (fun n => F (n, k))
      (qPochhammerInfIn (a * z) q / qPochhammerInfIn z q *
        twoPhiOneTerm (c / b) z (a * z) q b k) := by
    intro k
    have h := (hasSum_qBinomial_theorem hq a (hzq k)).mul_left (B k * b ^ k)
    have hazq : a * (z * q ^ k) = a * z * q ^ k := (mul_assoc a z (q ^ k)).symm
    rw [hazq, qPochhammerInfIn_mul_pow_div (a * z) hq k (hazn k),
      qPochhammerInfIn_mul_pow_div z hq k (hzn k)] at h
    have hval : B k * b ^ k * (qPochhammerInfIn (a * z) q / finiteQPochhammerIn (a * z) q k /
        (qPochhammerInfIn z q / finiteQPochhammerIn z q k)) =
        qPochhammerInfIn (a * z) q / qPochhammerInfIn z q *
          twoPhiOneTerm (c / b) z (a * z) q b k := by
      rw [hB, twoPhiOneTerm, div_div_div_eq]
      ring
    rw [hval] at h
    refine h.congr_fun fun n => ?_
    rw [hF, hA, mul_pow, ← pow_mul, Nat.mul_comm k n]
    ring
  -- the two iterated sums are the same double sum
  have hsum1 : HasSum (fun n => qPochhammerInfIn c q / qPochhammerInfIn b q *
      twoPhiOneTerm a b c q z n) (∑' p, F p) :=
    hFsum.hasSum.prod_fiberwise hrow
  have hswap : Summable fun p : ℕ × ℕ => F p.swap := hFsum.prod_symm
  have hsum2 : HasSum (fun k => qPochhammerInfIn (a * z) q / qPochhammerInfIn z q *
      twoPhiOneTerm (c / b) z (a * z) q b k) (∑' p, F p) := by
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq F]
    exact hswap.hasSum.prod_fiberwise hcol
  have hLHS : twoPhiOne a b c q z = qPochhammerInfIn b q / qPochhammerInfIn c q * ∑' p, F p := by
    refine ((hsum1.mul_left (qPochhammerInfIn b q / qPochhammerInfIn c q)).congr_fun
      fun n => ?_).tsum_eq
    rw [← mul_assoc, div_mul_div_comm, mul_comm (qPochhammerInfIn b q) (qPochhammerInfIn c q),
      div_self (mul_ne_zero hc hbinf), one_mul]
  have hRHS : ∑' p, F p = qPochhammerInfIn (a * z) q / qPochhammerInfIn z q *
      twoPhiOne (c / b) z (a * z) q b := by
    rw [← hsum2.tsum_eq, tsum_mul_left]
    rfl
  rw [hLHS, hRHS]
  ring

end Fabius
