import FabiusFunction.BaileyPairs
import FabiusFunction.QBinomialCauchy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# The full Bailey lemma

If `(α, β)` is a Bailey pair relative to `a`, `ρ₁ρ₂ ≠ 0`, and `A = aq/(ρ₁ρ₂)`, then

  `α'_n = (ρ₁;q)_n (ρ₂;q)_n A^n / ((aq/ρ₁;q)_n (aq/ρ₂;q)_n) · α_n`,
  `β'_n = ∑_{j ≤ n} (ρ₁;q)_j (ρ₂;q)_j (A;q)_{n-j} A^j / ((q;q)_{n-j} (aq/ρ₁;q)_n (aq/ρ₂;q)_n) · β_j`

is again a Bailey pair relative to `a` (`IsBaileyPair.transform`, qg:thm-bailey-lemma).
Substituting the Bailey relation and interchanging the sums, the coefficient of `α_r` is an
inner sum which, after the factorisations `(ρ;q)_{r+k} = (ρ;q)_r (ρq^r;q)_k`,
`(aq;q)_{2r+k} = (aq;q)_{2r} (c;q)_k` (`c = aq^{2r+1}`), `(q;q)_N = (q;q)_k (q;q)_{N-k} [N,k]_q`
and `(c;q)_N = (c;q)_k (cq^k;q)_{N-k}`, is the second finite Cauchy identity
`finite_qCauchy_second_identity` with `x = ρ₁q^r`, `y = ρ₂q^r`, `z = A` (`bailey_full_inner_sum`);
this replaces the reversal-and-Pfaff–Saalschütz route of the text (which needs the temporary
denominators `(q^{1-N}/A;q)_N ≠ 0`) by a polynomial identity valid without any restriction.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {K : Type*} [Field K]

/-- The transformed `α` of the full Bailey lemma. -/
def baileyTransformAlpha (a q ρ₁ ρ₂ : K) (α : ℕ → K) (n : ℕ) : K :=
  finiteQPochhammerIn ρ₁ q n * finiteQPochhammerIn ρ₂ q n * (a * q / (ρ₁ * ρ₂)) ^ n /
    (finiteQPochhammerIn (a * q / ρ₁) q n * finiteQPochhammerIn (a * q / ρ₂) q n) * α n

/-- The transformed `β` of the full Bailey lemma. -/
def baileyTransformBeta (a q ρ₁ ρ₂ : K) (β : ℕ → K) (n : ℕ) : K :=
  ∑ j ∈ range (n + 1),
    finiteQPochhammerIn ρ₁ q j * finiteQPochhammerIn ρ₂ q j *
        finiteQPochhammerIn (a * q / (ρ₁ * ρ₂)) q (n - j) * (a * q / (ρ₁ * ρ₂)) ^ j /
      (finiteQPochhammerIn q q (n - j) *
        (finiteQPochhammerIn (a * q / ρ₁) q n * finiteQPochhammerIn (a * q / ρ₂) q n)) * β j

/-- The inner sum of the full Bailey lemma, evaluated by the second finite Cauchy identity:
`∑_{k ≤ N} (x;q)_k (y;q)_k (A;q)_{N-k} A^k / ((q;q)_{N-k} (q;q)_k (xyA;q)_k)
  = (xA;q)_N (yA;q)_N / ((q;q)_N (xyA;q)_N)`. -/
theorem bailey_full_inner_sum {q : K} (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) (x y A : K)
    (hc : ∀ n, finiteQPochhammerIn (x * y * A) q n ≠ 0) (N : ℕ) :
    ∑ k ∈ range (N + 1),
        finiteQPochhammerIn x q k * finiteQPochhammerIn y q k * finiteQPochhammerIn A q (N - k) *
          A ^ k / (finiteQPochhammerIn q q (N - k) *
            (finiteQPochhammerIn q q k * finiteQPochhammerIn (x * y * A) q k)) =
      finiteQPochhammerIn (x * A) q N * finiteQPochhammerIn (y * A) q N /
        (finiteQPochhammerIn q q N * finiteQPochhammerIn (x * y * A) q N) := by
  have hC := finite_qCauchy_second_identity q x y A N
  have hterm : ∀ k ∈ range (N + 1),
      finiteQPochhammerIn x q k * finiteQPochhammerIn y q k * finiteQPochhammerIn A q (N - k) *
          A ^ k / (finiteQPochhammerIn q q (N - k) *
            (finiteQPochhammerIn q q k * finiteQPochhammerIn (x * y * A) q k)) =
      gaussianBinomial q N k * finiteQPochhammerIn x q k * finiteQPochhammerIn y q k * A ^ k *
          finiteQPochhammerIn A q (N - k) * finiteQPochhammerIn (x * y * A * q ^ k) q (N - k) /
        (finiteQPochhammerIn q q N * finiteQPochhammerIn (x * y * A) q N) := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h1 : finiteQPochhammerIn q q N =
        finiteQPochhammerIn q q k * finiteQPochhammerIn q q (N - k) * gaussianBinomial q N k :=
      finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q hkN
    have h2 : finiteQPochhammerIn (x * y * A) q N =
        finiteQPochhammerIn (x * y * A) q k * finiteQPochhammerIn (x * y * A * q ^ k) q (N - k) := by
      rw [← finiteQPochhammerIn_add, Nat.add_sub_cancel' hkN]
    have h3 : gaussianBinomial q N k ≠ 0 := by
      intro h0
      apply hq N
      rw [h1, h0, mul_zero]
    have h4 : finiteQPochhammerIn (x * y * A * q ^ k) q (N - k) ≠ 0 := by
      intro h0
      apply hc N
      rw [h2, h0, mul_zero]
    have h5 := hq k
    have h6 := hq (N - k)
    have h7 := hc k
    rw [h1, h2]
    field_simp
  rw [sum_congr rfl hterm, ← sum_div, ← hC]

/-- **The full Bailey lemma** (qg:thm-bailey-lemma): the transformed pair is a Bailey pair
relative to `a`. -/
theorem IsBaileyPair.transform {a q ρ₁ ρ₂ : K} {α β : ℕ → K} (h : IsBaileyPair a q α β)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0)
    (h₁ : ∀ n, finiteQPochhammerIn (a * q / ρ₁) q n ≠ 0)
    (h₂ : ∀ n, finiteQPochhammerIn (a * q / ρ₂) q n ≠ 0) :
    IsBaileyPair a q (baileyTransformAlpha a q ρ₁ ρ₂ α) (baileyTransformBeta a q ρ₁ ρ₂ β) := by
  intro n
  unfold baileyTransformBeta
  set A := a * q / (ρ₁ * ρ₂) with hA
  set D := finiteQPochhammerIn (a * q / ρ₁) q n * finiteQPochhammerIn (a * q / ρ₂) q n with hD
  have hD0 : D ≠ 0 := mul_ne_zero (h₁ n) (h₂ n)
  -- the coefficient of `α_r`
  have hcoef : ∀ r ∈ range (n + 1),
      ∑ j ∈ Ico r (n + 1),
        finiteQPochhammerIn ρ₁ q j * finiteQPochhammerIn ρ₂ q j * finiteQPochhammerIn A q (n - j) *
            A ^ j / (finiteQPochhammerIn q q (n - j) * D) /
          (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r)) =
      finiteQPochhammerIn ρ₁ q r * finiteQPochhammerIn ρ₂ q r * A ^ r /
          (finiteQPochhammerIn (a * q / ρ₁) q r * finiteQPochhammerIn (a * q / ρ₂) q r) /
        (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r)) := by
    intro r hr
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
    rw [sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 by omega]
    set N := n - r with hN
    set x := ρ₁ * q ^ r with hx
    set y := ρ₂ * q ^ r with hy
    have hxyA : x * y * A = a * q * q ^ (2 * r) := by
      rw [hx, hy, hA]
      field_simp
      ring
    have hc : ∀ m, finiteQPochhammerIn (x * y * A) q m ≠ 0 := fun m => by
      rw [hxyA]
      have h4 := ha (2 * r + m)
      rw [finiteQPochhammerIn_add (a * q) q (2 * r) m] at h4
      exact right_ne_zero_of_mul h4
    have hinner := bailey_full_inner_sum hq x y A hc N
    -- rewrite each term of the sum into the inner-sum form
    have hterm : ∀ k ∈ range (N + 1),
        finiteQPochhammerIn ρ₁ q (r + k) * finiteQPochhammerIn ρ₂ q (r + k) *
              finiteQPochhammerIn A q (n - (r + k)) * A ^ (r + k) /
            (finiteQPochhammerIn q q (n - (r + k)) * D) /
          (finiteQPochhammerIn q q (r + k - r) * finiteQPochhammerIn (a * q) q (r + k + r)) =
        finiteQPochhammerIn ρ₁ q r * finiteQPochhammerIn ρ₂ q r * A ^ r /
            (D * finiteQPochhammerIn (a * q) q (2 * r)) *
          (finiteQPochhammerIn x q k * finiteQPochhammerIn y q k * finiteQPochhammerIn A q (N - k) *
            A ^ k / (finiteQPochhammerIn q q (N - k) *
              (finiteQPochhammerIn q q k * finiteQPochhammerIn (x * y * A) q k))) := by
      intro k hk
      rw [show n - (r + k) = N - k by omega, Nat.add_sub_cancel_left,
        show r + k + r = 2 * r + k by ring, finiteQPochhammerIn_add ρ₁ q r k,
        finiteQPochhammerIn_add ρ₂ q r k, finiteQPochhammerIn_add (a * q) q (2 * r) k, pow_add,
        hxyA]
      have h1 := hq (N - k)
      have h2 := hq k
      have h3 := ha (2 * r)
      have h4 := ha (2 * r + k)
      rw [finiteQPochhammerIn_add (a * q) q (2 * r) k] at h4
      have h5 : finiteQPochhammerIn (a * q * q ^ (2 * r)) q k ≠ 0 := right_ne_zero_of_mul h4
      rw [← hx, ← hy]
      field_simp
    rw [sum_congr rfl hterm, ← mul_sum, hinner]
    -- the remaining cancellations
    have e1 : finiteQPochhammerIn (a * q / ρ₁) q n =
        finiteQPochhammerIn (a * q / ρ₁) q r * finiteQPochhammerIn (y * A) q N := by
      rw [show n = r + N by omega, finiteQPochhammerIn_add]
      congr 2
      rw [hy, hA]
      field_simp
    have e2 : finiteQPochhammerIn (a * q / ρ₂) q n =
        finiteQPochhammerIn (a * q / ρ₂) q r * finiteQPochhammerIn (x * A) q N := by
      rw [show n = r + N by omega, finiteQPochhammerIn_add]
      congr 2
      rw [hx, hA]
      field_simp
    have e3 : finiteQPochhammerIn (a * q) q (n + r) =
        finiteQPochhammerIn (a * q) q (2 * r) * finiteQPochhammerIn (x * y * A) q N := by
      rw [show n + r = 2 * r + N by omega, finiteQPochhammerIn_add, hxyA]
    rw [hD, e1, e2, e3]
    have f1 := h₁ r
    have f2 := h₂ r
    have f3 := ha (2 * r)
    have f4 := hq N
    have f5 := hc N
    have f6 : finiteQPochhammerIn (y * A) q N ≠ 0 := by
      intro h0
      apply h₁ n
      rw [e1, h0, mul_zero]
    have f7 : finiteQPochhammerIn (x * A) q N ≠ 0 := by
      intro h0
      apply h₂ n
      rw [e2, h0, mul_zero]
    rw [div_mul_div_comm, div_div, div_eq_div_iff (by (repeat' apply mul_ne_zero); all_goals assumption)
      (by (repeat' apply mul_ne_zero); all_goals assumption)]
    ring
  -- substitute the Bailey relation and interchange the sums
  calc (∑ j ∈ range (n + 1),
        finiteQPochhammerIn ρ₁ q j * finiteQPochhammerIn ρ₂ q j * finiteQPochhammerIn A q (n - j) *
          A ^ j / (finiteQPochhammerIn q q (n - j) * D) * β j)
      = ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1),
          α r * (finiteQPochhammerIn ρ₁ q j * finiteQPochhammerIn ρ₂ q j *
            finiteQPochhammerIn A q (n - j) * A ^ j / (finiteQPochhammerIn q q (n - j) * D) /
            (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        refine sum_congr rfl fun j _ => ?_
        rw [h j, mul_sum]
        refine sum_congr rfl fun r _ => ?_
        ring
    _ = ∑ r ∈ range (n + 1), ∑ j ∈ Ico r (n + 1),
          α r * (finiteQPochhammerIn ρ₁ q j * finiteQPochhammerIn ρ₂ q j *
            finiteQPochhammerIn A q (n - j) * A ^ j / (finiteQPochhammerIn q q (n - j) * D) /
            (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        refine sum_comm' fun j r => ?_
        simp only [mem_range, mem_Ico]
        constructor
        · intro hjr
          omega
        · intro hjr
          omega
    _ = ∑ r ∈ range (n + 1), baileyTransformAlpha a q ρ₁ ρ₂ α r /
          (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r)) := by
        refine sum_congr rfl fun r hr => ?_
        rw [← mul_sum, hcoef r hr]
        simp only [baileyTransformAlpha, ← hA]
        ring

end Fabius
