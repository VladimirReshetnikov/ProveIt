import FabiusFunction.BaileyPairs
import FabiusFunction.QDifferenceAnnihilation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp

/-!
# Bailey inversion

For `a ≠ 1` (and nonvanishing denominators), the Bailey relation
`β_n = ∑_{r ≤ n} α_r / ((q;q)_{n-r} (aq;q)_{n+r})` is equivalent to

  `α_n = (1 - aq^{2n})/(1 - a) ∑_{j ≤ n} (a;q)_{n+j}/(q;q)_{n-j} (-1)^{n-j} q^{C(n-j,2)} β_j`

(`isBaileyPair_iff_eq_baileyInverse`).  Substituting the relation into the inverse formula,
the coefficient of `α_r` is `1` for `r = n` and, for `r < n`, `N = n - r`, a `q`-difference
sum `∑_{s ≤ N} (-1)^{N-s} q^{C(N-s,2)} [N,s]_q P(q^s)` against the polynomial
`P(x) = (aq^{2r+1}x;q)_{N-1}` of degree `N-1 < N`, which vanishes
(`qDifference_sum_eval₂_eq_zero_of_degree_lt`).  This shows that the inverse formula is a
left inverse of the Bailey transform (`IsBaileyPair.eq_baileyInverse`); since every `β` is
the Bailey transform of some `α` (forward substitution, `baileySolve`), it is a two-sided
inverse.

## Main declarations

* `baileyInverseKernel`, `baileyInverse`, `IsBaileyPair.eq_baileyInverse`.
* `baileySolve`, `isBaileyPair_baileySolve`, `exists_isBaileyPair`.
* `isBaileyPair_iff_eq_baileyInverse`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

variable {K : Type*} [Field K]

/-- The kernel of the Bailey inverse: `(a;q)_{n+j}/(q;q)_{n-j} · (-1)^{n-j} q^{C(n-j,2)}`. -/
def baileyInverseKernel (a q : K) (n j : ℕ) : K :=
  finiteQPochhammerIn a q (n + j) / finiteQPochhammerIn q q (n - j) *
    ((-1) ^ (n - j) * q ^ (n - j).choose 2)

/-- The Bailey inverse
`α_n = (1 - aq^{2n})/(1 - a) ∑_{j ≤ n} (a;q)_{n+j}/(q;q)_{n-j} (-1)^{n-j} q^{C(n-j,2)} β_j`. -/
def baileyInverse (a q : K) (β : ℕ → K) (n : ℕ) : K :=
  (1 - a * q ^ (2 * n)) / (1 - a) * ∑ j ∈ range (n + 1), baileyInverseKernel a q n j * β j

/-- `(1 - aq^{2n}) (a;q)_{2n} = (1 - a) (aq;q)_{2n}`. -/
theorem one_sub_mul_pow_mul_finiteQPochhammerIn_two_mul (a q : K) (n : ℕ) :
    (1 - a * q ^ (2 * n)) * finiteQPochhammerIn a q (2 * n) =
      (1 - a) * finiteQPochhammerIn (a * q) q (2 * n) := by
  cases n with
  | zero => simp [finiteQPochhammerIn]
  | succ m =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, finiteQPochhammerIn_succ_shift a q (2 * m + 1),
        finiteQPochhammerIn_succ (a * q) q (2 * m + 1)]
      ring

/-- The inverse formula is a left inverse of the Bailey transform: for a Bailey pair,
`α_n = baileyInverse a q β n`. -/
theorem IsBaileyPair.eq_baileyInverse {a q : K} {α β : ℕ → K} (h : IsBaileyPair a q α β)
    (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0)
    (ha1 : a ≠ 1) (n : ℕ) : α n = baileyInverse a q β n := by
  have h1a : (1 : K) - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  have h0 : finiteQPochhammerIn q q 0 = 1 := by simp [finiteQPochhammerIn]
  -- the coefficient of `α_r` after substituting the Bailey relation
  have hcoef : ∀ r ∈ range (n + 1),
      (1 - a * q ^ (2 * n)) / (1 - a) * ∑ j ∈ Ico r (n + 1), baileyInverseKernel a q n j /
        (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r)) =
      if r = n then 1 else 0 := by
    intro r hr
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
    rcases eq_or_lt_of_le hrn with heq | hlt
    · subst heq
      rw [if_pos rfl, Nat.Ico_succ_singleton, sum_singleton]
      unfold baileyInverseKernel
      rw [Nat.sub_self, ← two_mul, h0, Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2)]
      simp only [pow_zero, div_one, mul_one, one_mul]
      rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1a (ha (2 * r)))]
      exact one_sub_mul_pow_mul_finiteQPochhammerIn_two_mul a q r
    · rw [if_neg hlt.ne, sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 by omega]
      set N := n - r with hN
      have hN1 : 1 ≤ N := by omega
      set c : K := a * q ^ (2 * r + 1) with hc
      set P : K[X] := ∏ i ∈ range (N - 1), (1 - C (c * q ^ i) * X) with hP
      have hPdeg : P.degree < (N : WithBot ℕ) := by
        have h1 : ∀ i ∈ range (N - 1), (1 - C (c * q ^ i) * X : K[X]).natDegree ≤ 1 :=
          fun i _ => (natDegree_sub_le _ _).trans (max_le
            (by rw [natDegree_one]; exact zero_le_one)
            ((natDegree_C_mul_le _ _).trans natDegree_X_le))
        have h2 : P.natDegree ≤ N - 1 := by
          refine (natDegree_prod_le _ _).trans ?_
          calc ∑ i ∈ range (N - 1), (1 - C (c * q ^ i) * X : K[X]).natDegree
              ≤ ∑ i ∈ range (N - 1), 1 := sum_le_sum h1
            _ = N - 1 := by simp
        refine lt_of_le_of_lt degree_le_natDegree ?_
        exact_mod_cast (show P.natDegree < N by omega)
      have hPeval : ∀ s, P.eval₂ (RingHom.id K) (q ^ s) =
          finiteQPochhammerIn (c * q ^ s) q (N - 1) := by
        intro s
        rw [hP, eval₂_finsetProd]
        unfold finiteQPochhammerIn
        refine prod_congr rfl fun i _ => ?_
        simp only [eval₂_sub, eval₂_one, eval₂_mul, eval₂_C, eval₂_X, RingHom.id_apply]
        ring
      have hann := qDifference_sum_eval₂_eq_zero_of_degree_lt (RingHom.id K) q N P hPdeg
      have hterm : ∀ s ∈ range (N + 1),
          baileyInverseKernel a q n (r + s) /
            (finiteQPochhammerIn q q (r + s - r) * finiteQPochhammerIn (a * q) q (r + s + r)) =
          (1 - a) / finiteQPochhammerIn q q N *
            (gaussianBinomialInverseKernel q N s * P.eval₂ (RingHom.id K) (q ^ s)) := by
        intro s hs
        have hsN : s ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hs)
        unfold baileyInverseKernel gaussianBinomialInverseKernel
        rw [hPeval, show n - (r + s) = N - s by omega, Nat.add_sub_cancel_left,
          show r + s + r = 2 * r + s by ring,
          show n + (r + s) = (2 * r + s + 1) + (N - 1) by omega,
          finiteQPochhammerIn_add a q (2 * r + s + 1) (N - 1),
          finiteQPochhammerIn_succ_shift a q (2 * r + s),
          show a * q ^ (2 * r + s + 1) = c * q ^ s by rw [hc]; ring]
        have hG := finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q hsN
        have hGne : gaussianBinomial q N s ≠ 0 := by
          intro h0'
          apply hq N
          rw [hG, h0', mul_zero]
        have h1 := hq s
        have h2 := hq (N - s)
        have h3 := ha (2 * r + s)
        rw [hG]
        field_simp
      rw [sum_congr rfl hterm, ← mul_sum, hann, mul_zero, mul_zero]
  symm
  unfold baileyInverse
  calc (1 - a * q ^ (2 * n)) / (1 - a) *
        ∑ j ∈ range (n + 1), baileyInverseKernel a q n j * β j
      = (1 - a * q ^ (2 * n)) / (1 - a) * ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1),
          α r * (baileyInverseKernel a q n j /
            (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [h j, mul_sum]
        refine sum_congr rfl fun r _ => ?_
        ring
    _ = (1 - a * q ^ (2 * n)) / (1 - a) * ∑ r ∈ range (n + 1), ∑ j ∈ Ico r (n + 1),
          α r * (baileyInverseKernel a q n j /
            (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        congr 1
        refine sum_comm' fun j r => ?_
        simp only [mem_range, mem_Ico]
        constructor
        · intro hjr
          omega
        · intro hjr
          omega
    _ = ∑ r ∈ range (n + 1), α r * ((1 - a * q ^ (2 * n)) / (1 - a) *
          ∑ j ∈ Ico r (n + 1), baileyInverseKernel a q n j /
            (finiteQPochhammerIn q q (j - r) * finiteQPochhammerIn (a * q) q (j + r))) := by
        simp only [mul_sum]
        refine sum_congr rfl fun r _ => sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ r ∈ range (n + 1), α r * (if r = n then 1 else 0) :=
        sum_congr rfl fun r hr => by rw [hcoef r hr]
    _ = α n := by simp

/-- Forward substitution: the sequence `α` with
`β_n = ∑_{r ≤ n} α_r / ((q;q)_{n-r} (aq;q)_{n+r})` for a given `β`. -/
noncomputable def baileySolve (a q : K) (β : ℕ → K) : ℕ → K
  | n => finiteQPochhammerIn (a * q) q (2 * n) *
      (β n - ∑ r : Fin n, baileySolve a q β r /
        (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r)))
termination_by n => n
decreasing_by all_goals exact r.isLt

/-- Every `β` is the Bailey transform of `baileySolve a q β`. -/
theorem isBaileyPair_baileySolve (a q : K) (β : ℕ → K)
    (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0) :
    IsBaileyPair a q (baileySolve a q β) β := by
  intro n
  have h0 : finiteQPochhammerIn q q 0 = 1 := by simp [finiteQPochhammerIn]
  rw [sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun r => baileySolve a q β r /
    (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r))) n]
  conv_rhs => rw [baileySolve]
  rw [Nat.sub_self, h0, ← two_mul, one_mul, mul_div_cancel_left₀ _ (ha (2 * n))]
  ring

/-- The Bailey transform is surjective. -/
theorem exists_isBaileyPair (a q : K) (β : ℕ → K)
    (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0) : ∃ α, IsBaileyPair a q α β :=
  ⟨_, isBaileyPair_baileySolve a q β ha⟩

/-- **Bailey inversion** (thm:bailey-inversion): for `a ≠ 1`, `(α, β)` is a Bailey pair
relative to `a` if and only if `α = baileyInverse a q β`. -/
theorem isBaileyPair_iff_eq_baileyInverse {a q : K} {α β : ℕ → K}
    (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0)
    (ha1 : a ≠ 1) :
    IsBaileyPair a q α β ↔ ∀ n, α n = baileyInverse a q β n := by
  constructor
  · exact fun h => h.eq_baileyInverse hq ha ha1
  · intro hα
    obtain ⟨α', hα'⟩ := exists_isBaileyPair a q β ha
    have hαα' : α = α' := funext fun n => by rw [hα n, hα'.eq_baileyInverse hq ha ha1 n]
    rw [hαα']
    exact hα'

end Fabius
