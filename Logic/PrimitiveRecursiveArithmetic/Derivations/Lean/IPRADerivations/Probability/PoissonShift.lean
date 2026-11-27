import IPRADerivations.Combinatorics.BellDobinski
import IPRADerivations.Foundations.ContractProducts
import IPRADerivations.Core.OrderCertificates

/-!
# The finite shift identity of the Poisson mean

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:poisson` ("Poisson"), the finite
stage of its proof: "At finite stage, `∑_{k=0}^{N} k p_k = λ e^{−λ} ∑_{j=0}^{N−1} λ^j/j!`. This is the
exact shift identity `k/k! = 1/(k − 1)!`."

* `kB t`: the body `k · t(k, x)`;
* `shift_identity`: for any weights with the ratio recurrence `(k + 1) β t(k + 1) = α t(k)` for `k < N`
  (the weights of a law with `p_{k+1}/p_k = λ/(k + 1)`, `λ = α/β`),
  `β ∑_{k<N+1} k t(k) = α ∑_{j<N} t(j)`, i.e. `∑_{k ≤ N} k p_k = λ ∑_{j ≤ N−1} p_j`;
* `ff_ratio`: `(k + 1) · M!/(k + 1)! = M!/k!` for `k < M`, with `M!/k! = (M)_{M−k}`;
* `poB`, `po_ratio`: the Poisson weights with `λ = a/b` on the scale `M! b^M`,
  `t(k) = a^k b^{M−k} M!/k!` (parameter `x = ⟨M, ⟨a, b⟩⟩`), satisfy the ratio recurrence;
* `poisson_shift`: `b ∑_{k ≤ M} k t(k) = a ∑_{j<M} t(j)`.

The factor `e^{−λ}` is common to both sides. The passage to the limit (the Taylor remainder of `e^λ` and
the geometric tail bound for `N > 2L`) is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.PoissonShift

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ff)
open LeanProofs.IPRA.Combinatorics.BellDobinski (ff_fact_k)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ContractProducts (shift_fstT shift_sndT)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The shift identity for a ratio recurrence -/

section Abstract

variable (t : PTm 2)

/-- `k · t(k, x)`. -/
def kB : PTm 2 := var 0 * t

theorem inst2_kB (k x : PTm n) : inst2 (kB t) k x = k * inst2 t k x := by
  simp [inst2, kB]

theorem shift_base (α β x : PTm n) :
    Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ zero) x ≐ α * ap2 (sumF t) zero x := by
  have s := sum_succ' (Γ := Γ) (kB t) zero x
  rw [inst2_kB] at s
  ipra_lc 𝔟 β * natEq s + 𝔟 β * natEq (sum_zero (Γ := Γ) (kB t) x) - 𝔟 α * natEq (sum_zero (Γ := Γ) t x)

theorem shift_step {α β K x : PTm n}
    (hr : Γ ⊢[PRAAx] succ K * (β * inst2 t (succ K) x) ≐ α * inst2 t K x)
    (ih : Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ K) x ≐ α * ap2 (sumF t) K x) :
    Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ (succ K)) x ≐ α * ap2 (sumF t) (succ K) x := by
  have s₁ := sum_succ' (Γ := Γ) (kB t) (succ K) x
  rw [inst2_kB] at s₁
  ipra_lc 𝔟 β * natEq s₁ + natEq ih + natEq hr - 𝔟 α * natEq (sum_succ' (Γ := Γ) t K x)

theorem shift_guard {α β K N x : PTm n}
    (hK : Γ ⊢[PRAAx] le (succ K) N)
    (hr : Γ ⊢[PRAAx] lt K N ⟶ (succ K * (β * inst2 t (succ K) x) ≐ α * inst2 t K x))
    (ih : Γ ⊢[PRAAx] le K N ⟶ (β * ap2 (sumF (kB t)) (succ K) x ≐ α * ap2 (sumF t) K x)) :
    Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ (succ K)) x ≐ α * ap2 (sumF t) (succ K) x :=
  shift_step t (Prf.impE hr hK) (Prf.impE ih (le_trans (le_succ_self K) hK))

theorem shift_all {α β N x : PTm n}
    (hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (succ (var 0) * (Syn.shift β * inst2 t (succ (var 0)) (Syn.shift x)) ≐
        Syn.shift α * inst2 t (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (Syn.shift β * ap2 (sumF (kB t)) (succ (var 0)) (Syn.shift x) ≐
        Syn.shift α * ap2 (sumF t) (var 0) (Syn.shift x))) := by
  refine qfIndAllUpTo N trivial ?_ ?_
  · simpa using shift_base (Γ := Γ) t α β x
  · simp
    exact .impI (shift_step t (.impE hr.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

/-- `prop:poisson`, the finite stage: weights with `(k + 1) β t(k + 1) = α t(k)` for `k < N` satisfy
`β ∑_{k<N+1} k t(k) = α ∑_{j<N} t(j)`. -/
theorem shift_identity {α β N x : PTm n}
    (hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (succ (var 0) * (Syn.shift β * inst2 t (succ (var 0)) (Syn.shift x)) ≐
        Syn.shift α * inst2 t (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ N) x ≐ α * ap2 (sumF t) N x := by
  exact .impE (by simpa using Prf.allE N (shift_all t hr)) (le_refl N)

end Abstract

/-! ## The Poisson weights -/

/-- `(k + 1) · M!/(k + 1)! = M!/k!` for `k < M`, with `M!/k! = (M)_{M−k}`. -/
theorem ff_ratio {k M : PTm n} (h : Γ ⊢[PRAAx] lt k M) :
    Γ ⊢[PRAAx] succ k * ff M (monus M (succ k)) ≐ ff M (monus M k) := by
  have h' : Γ ⊢[PRAAx] le (succ k) M := h
  refine mul_cancel (fact_pos k) ?_
  ipra_lc natEq (ff_fact_k h') - natEq (ff_fact_k (le_of_lt h)) -
    𝔟(ff M (monus M (succ k))) * natEq (fact_succ (Γ := Γ) k zero)

alias monus_pred := Common.monus_succ_of_lt

/-- The ratio recurrence of `t(k) = a^k b^{M−k} M!/k!`: `(k + 1) b t(k + 1) = a t(k)` for `k < M`. -/
theorem po_ratio {k M a b : PTm n} (h : Γ ⊢[PRAAx] lt k M) :
    Γ ⊢[PRAAx] succ k * (b * (pw a (succ k) * pw b (monus M (succ k)) * ff M (monus M (succ k)))) ≐
      a * (pw a k * pw b (monus M k) * ff M (monus M k)) := by
  ipra_lc (𝔟 k + 1) * 𝔟 b * 𝔟(pw b (monus M (succ k))) * 𝔟(ff M (monus M (succ k))) * natEq (pw_succ (Γ := Γ) a k) -
    𝔟 a * 𝔟(pw a k) * 𝔟(ff M (monus M k)) * natEq ((congrAp2 powF (monus_pred h) (.eqRefl b)).eqTrans (pw_succ (Γ := Γ) b (monus M (succ k)))) +
    𝔟 a * 𝔟(pw a k) * 𝔟(pw b (monus M (succ k))) * 𝔟 b * natEq (ff_ratio h)

/-- The Poisson weights `a^k b^{M−k} M!/k!` on the scale `M! b^M`; variables `0 = k`,
`1 = x = ⟨M, ⟨a, b⟩⟩`. -/
def poB : PTm 2 :=
  pw (fstT (sndT (var 1))) (var 0) * pw (sndT (sndT (var 1))) (monus (fstT (var 1)) (var 0)) *
    ff (fstT (var 1)) (monus (fstT (var 1)) (var 0))

theorem inst2_poB (k x : PTm n) :
    inst2 poB k x = pw (fstT (sndT x)) k * pw (sndT (sndT x)) (monus (fstT x) k) *
      ff (fstT x) (monus (fstT x) k) := by
  simp [inst2, poB]

/-- `prop:poisson`, the finite stage for the Poisson weights with `λ = a/b`, `M = fst x`,
`a = fst (snd x)`, `b = snd (snd x)`: `b ∑_{k ≤ M} k t(k) = a ∑_{j<M} t(j)`. -/
theorem poisson_shift (x : PTm n) :
    Γ ⊢[PRAAx] sndT (sndT x) * ap2 (sumF (kB poB)) (succ (fstT x)) x ≐
      fstT (sndT x) * ap2 (sumF poB) (fstT x) x := by
  refine shift_identity poB (.allI (.impI ?_))
  simp only [inst2_poB, shift_sndT, shift_fstT]
  exact po_ratio Prf.hyp0

end LeanProofs.IPRA.Probability.PoissonShift
