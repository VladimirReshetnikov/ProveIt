import FabiusFunction.BaileyPairs
import FabiusFunction.BaileyUnitPairs

/-!
# The iterated Bailey chain

Iterating the finite limiting Bailey lemma `t` times transforms a Bailey pair `(α, β)`
relative to `a` into the Bailey pair

  `α^{(t)}_n = a^{tn} q^{tn²} α_n`,
  `β^{(0)} = β`,  `β^{(t+1)}_n = ∑_{j ≤ n} a^j q^{j²} β^{(t)}_j / (q;q)_{n-j}`

(`IsBaileyPair.chain`, qg:lem-bailey-chain-iterate).  Unfolding the recursion, `β^{(t)}_n` is
the `t`-fold sum over `n ≥ r_1 ≥ ⋯ ≥ r_t ≥ 0` of
`a^{r_1+⋯+r_t} q^{r_1²+⋯+r_t²} β_{r_t} / ((q;q)_{n-r_1} ∏ (q;q)_{r_ℓ-r_{ℓ+1}})`, which is the
closed form displayed in the text.  For the unit sequence `β = δ`, `β^{(1)}_n = 1/(q;q)_n`
(`baileyChainBeta_unit_one`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {K : Type*} [Field K]

/-- The `t`-fold chain transform of `α`: `α^{(t)}_n = a^{tn} q^{tn²} α_n`. -/
def baileyChainAlpha (a q : K) (α : ℕ → K) (t n : ℕ) : K :=
  a ^ (t * n) * q ^ (t * (n * n)) * α n

/-- The `t`-fold chain transform of `β`: `β^{(0)} = β` and
`β^{(t+1)}_n = ∑_{j ≤ n} a^j q^{j²} β^{(t)}_j / (q;q)_{n-j}`. -/
def baileyChainBeta (a q : K) (β : ℕ → K) : ℕ → ℕ → K
  | 0, n => β n
  | t + 1, n => ∑ j ∈ range (n + 1),
      a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * baileyChainBeta a q β t j

/-- Zero iterations leave `α` alone: `α^{(0)}_n = a^0 q^0 α_n = α_n`, so `α^{(0)} = α` as
functions.  Together with `baileyChainBeta_zero` this is the base case of the induction in
`IsBaileyPair.chain`. -/
@[simp] theorem baileyChainAlpha_zero (a q : K) (α : ℕ → K) : baileyChainAlpha a q α 0 = α := by
  funext n
  simp [baileyChainAlpha]

/-- Zero iterations leave `β` alone: `β^{(0)} = β`, the first branch of the recursion defining
`baileyChainBeta`, hence true by `rfl`. -/
@[simp] theorem baileyChainBeta_zero (a q : K) (β : ℕ → K) : baileyChainBeta a q β 0 = β := rfl

/-- One step of the chain, in rewritable form:
`β^{(t+1)}_n = ∑_{j ≤ n} a^j q^{j²} β^{(t)}_j / (q;q)_{n-j}`.  This is the second branch of the
recursion defining `baileyChainBeta` (so again `rfl`), stated as an equation between terms rather
than between the two functions, which is the shape needed to unfold a single application of the
finite limiting Bailey lemma inside a proof. -/
theorem baileyChainBeta_succ (a q : K) (β : ℕ → K) (t n : ℕ) :
    baileyChainBeta a q β (t + 1) n = ∑ j ∈ range (n + 1),
      a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * baileyChainBeta a q β t j := rfl

/-- **The iterated Bailey chain** (qg:lem-bailey-chain-iterate): `t` applications of the finite
limiting Bailey lemma. -/
theorem IsBaileyPair.chain {a q : K} {α β : ℕ → K} (h : IsBaileyPair a q α β)
    (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) (ha : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0)
    (t : ℕ) : IsBaileyPair a q (baileyChainAlpha a q α t) (baileyChainBeta a q β t) := by
  induction t with
  | zero =>
      rw [baileyChainAlpha_zero, baileyChainBeta_zero]
      exact h
  | succ t ih =>
      have h' := ih.limit_step hq ha
      have e1 : (fun n => a ^ n * q ^ (n * n) * baileyChainAlpha a q α t n) =
          baileyChainAlpha a q α (t + 1) := by
        funext n
        simp only [baileyChainAlpha]
        ring
      have e2 : (fun n => ∑ j ∈ range (n + 1),
          a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * baileyChainBeta a q β t j) =
          baileyChainBeta a q β (t + 1) := rfl
      rw [e1, e2] at h'
      exact h'

/-- For the unit sequence `β = δ`, one chain step gives `β^{(1)}_n = 1/(q;q)_n`. -/
theorem baileyChainBeta_unit_one (a q : K) (n : ℕ) :
    baileyChainBeta a q unitBaileyBeta 1 n = (finiteQPochhammerIn q q n)⁻¹ := by
  rw [baileyChainBeta_succ, baileyChainBeta_zero,
    sum_eq_single_of_mem 0 (mem_range.mpr (Nat.succ_pos n)) (fun j _ hj => by
      simp [unitBaileyBeta, hj])]
  simp [unitBaileyBeta]

end Fabius
