import FabiusFunction.BaileyAux
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# Bailey pairs and the limiting Bailey lemma, finite form

A pair of sequences `(α_n), (β_n)` is a *Bailey pair relative to `a`* (with base `q`) if

  `β_n = ∑_{r=0}^{n} α_r / ((q;q)_{n-r} (aq;q)_{n+r})`  for every `n`

(`IsBaileyPair`).  The limiting Bailey lemma in finite form (`IsBaileyPair.limit_step`) says
that if `(α, β)` is a Bailey pair relative to `a`, so is

  `α'_n = a^n q^{n²} α_n`,  `β'_n = ∑_{j=0}^{n} a^j q^{j²} β_j / (q;q)_{n-j}`.

Substituting the Bailey relation into `β'_n` and interchanging the finite sums, the
coefficient of `α_r` is an inner sum over `s = j - r` which, after the change of variable
`A = aq^{2r+1}` and the factorisations `(q;q)_N = (q;q)_s (q;q)_{N-s} [N,s]_q`,
`(aq;q)_{2r+N} = (aq;q)_{2r+s} (Aq^s;q)_{N-s}`, is exactly the auxiliary identity
`bailey_aux_sum` (`bailey_inner_sum`).

Throughout, the denominators are assumed nonzero: `(q;q)_n ≠ 0` and `(aq;q)_n ≠ 0` for all `n`.

## Main declarations

* `IsBaileyPair`, `bailey_inner_sum`, `IsBaileyPair.limit_step`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {K : Type*} [Field K]

/-- `IsBaileyPair a q α β`: `β_n = ∑_{r ≤ n} α_r / ((q;q)_{n-r} (aq;q)_{n+r})` for all `n`. -/
def IsBaileyPair (a q : K) (α β : ℕ → K) : Prop :=
  ∀ n, β n = ∑ r ∈ range (n + 1),
    α r / (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r))

/-- The inner sum of the limiting Bailey lemma: for `N, r ≥ 0`,
`∑_{s ≤ N} a^{r+s} q^{(r+s)²} / ((q;q)_{N-s} (q;q)_s (aq;q)_{2r+s})
  = a^r q^{r²} / ((q;q)_N (aq;q)_{2r+N})`. -/
theorem bailey_inner_sum {a q : K} (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0)
    (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0) (r N : ℕ) :
    ∑ s ∈ range (N + 1), a ^ (r + s) * q ^ ((r + s) * (r + s)) /
        (finiteQPochhammerIn q q (N - s) * (finiteQPochhammerIn q q s *
          finiteQPochhammerIn (a * q) q (2 * r + s))) =
      a ^ r * q ^ (r * r) /
        (finiteQPochhammerIn q q N * finiteQPochhammerIn (a * q) q (2 * r + N)) := by
  set A := a * q ^ (2 * r + 1) with hA
  have key := bailey_aux_sum q A N
  have hterm : ∀ s ∈ range (N + 1),
      a ^ (r + s) * q ^ ((r + s) * (r + s)) /
        (finiteQPochhammerIn q q (N - s) * (finiteQPochhammerIn q q s *
          finiteQPochhammerIn (a * q) q (2 * r + s))) =
      a ^ r * q ^ (r * r) /
          (finiteQPochhammerIn q q N * finiteQPochhammerIn (a * q) q (2 * r + N)) *
        (A ^ s * q ^ (s * (s - 1)) * gaussianBinomial q N s *
          finiteQPochhammerIn (A * q ^ s) q (N - s)) := by
    intro s hs
    have hsN : s ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hs)
    have h1 : finiteQPochhammerIn q q N =
        finiteQPochhammerIn q q s * finiteQPochhammerIn q q (N - s) * gaussianBinomial q N s :=
      finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q hsN
    have h2 : finiteQPochhammerIn (a * q) q (2 * r + N) =
        finiteQPochhammerIn (a * q) q (2 * r + s) * finiteQPochhammerIn (A * q ^ s) q (N - s) := by
      rw [show 2 * r + N = (2 * r + s) + (N - s) by omega, finiteQPochhammerIn_add]
      congr 2
      rw [hA]
      ring
    have hexp : a ^ (r + s) * q ^ ((r + s) * (r + s)) =
        a ^ r * q ^ (r * r) * (A ^ s * q ^ (s * (s - 1))) := by
      rw [hA]
      cases s with
      | zero => ring
      | succ t =>
          rw [Nat.add_sub_cancel]
          ring
    have h3 : gaussianBinomial q N s ≠ 0 := by
      intro h0
      apply hq N
      rw [h1, h0, mul_zero]
    have h4 : finiteQPochhammerIn (A * q ^ s) q (N - s) ≠ 0 := by
      intro h0
      apply ha (2 * r + N)
      rw [h2, h0, mul_zero]
    have h5 := hq s
    have h6 := hq (N - s)
    have h7 := ha (2 * r + s)
    rw [hexp, h1, h2]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, key, mul_one]

/-- **The limiting Bailey lemma, finite form** (thm:bailey-limit-finite): if `(α, β)` is a
Bailey pair relative to `a`, so is `(a^n q^{n²} α_n, ∑_{j ≤ n} a^j q^{j²} β_j / (q;q)_{n-j})`. -/
theorem IsBaileyPair.limit_step {a q : K} {α β : ℕ → K} (h : IsBaileyPair a q α β)
    (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0) :
    IsBaileyPair a q (fun n => a ^ n * q ^ (n * n) * α n)
      (fun n => ∑ j ∈ range (n + 1), a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * β j) := by
  intro n
  dsimp only
  calc (∑ j ∈ range (n + 1), a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * β j)
      = ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1),
          a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
            (α r / (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        refine sum_congr rfl fun j _ => ?_
        rw [h j, mul_sum]
    _ = ∑ r ∈ range (n + 1), ∑ j ∈ Ico r (n + 1),
          a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
            (α r / (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        refine sum_comm' fun j r => ?_
        simp only [mem_range, mem_Ico]
        constructor
        · intro hjr
          omega
        · intro hjr
          omega
    _ = ∑ r ∈ range (n + 1), a ^ r * q ^ (r * r) * α r /
          (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r)) := by
        refine sum_congr rfl fun r hr => ?_
        have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
        rw [sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 by omega]
        have hinner := bailey_inner_sum hq ha r (n - r)
        rw [show 2 * r + (n - r) = n + r by omega] at hinner
        calc ∑ s ∈ range (n - r + 1),
              a ^ (r + s) * q ^ ((r + s) * (r + s)) / finiteQPochhammerIn q q (n - (r + s)) *
                (α r / (finiteQPochhammerIn q q (r + s - r) *
                  finiteQPochhammerIn (a * q) q (r + s + r)))
            = α r * ∑ s ∈ range (n - r + 1), a ^ (r + s) * q ^ ((r + s) * (r + s)) /
                (finiteQPochhammerIn q q (n - r - s) * (finiteQPochhammerIn q q s *
                  finiteQPochhammerIn (a * q) q (2 * r + s))) := by
              rw [mul_sum]
              refine sum_congr rfl fun s _ => ?_
              rw [show n - (r + s) = n - r - s by omega, Nat.add_sub_cancel_left,
                show r + s + r = 2 * r + s by ring]
              ring
          _ = _ := by
              rw [hinner]
              ring

end Fabius
