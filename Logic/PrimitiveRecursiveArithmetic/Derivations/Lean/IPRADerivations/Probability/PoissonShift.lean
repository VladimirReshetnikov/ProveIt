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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ff)
open LeanProofs.IPRA.Combinatorics.BellDobinski (ff_fact_k)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ContractProducts (shift_fstT shift_sndT)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

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
  have es := natEq s
  have z₁ := natEq (sum_zero (Γ := Γ) (kB t) x)
  have z₂ := natEq (sum_zero (Γ := Γ) t x)
  apply deriveNat; ipra_simps
  linear_combination 𝔟 β * es + 𝔟 β * z₁ - 𝔟 α * z₂

theorem shift_step {α β K x : PTm n}
    (hr : Γ ⊢[PRAAx] succ K * (β * inst2 t (succ K) x) ≐ α * inst2 t K x)
    (ih : Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ K) x ≐ α * ap2 (sumF t) K x) :
    Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ (succ K)) x ≐ α * ap2 (sumF t) (succ K) x := by
  have s₁ := sum_succ' (Γ := Γ) (kB t) (succ K) x
  rw [inst2_kB] at s₁
  have e₁ := natEq s₁
  have e₂ := natEq (sum_succ' (Γ := Γ) t K x)
  have r := natEq hr
  have i := natEq ih
  apply deriveNat; ipra_simps
  linear_combination 𝔟 β * e₁ + i + r - 𝔟 α * e₂

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
  refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
  · have e : (le (var 0) (Syn.shift N) ⟶
          (Syn.shift β * ap2 (sumF (kB t)) (succ (var 0)) (Syn.shift x) ≐
            Syn.shift α * ap2 (sumF t) (var 0) (Syn.shift x))).subst (Syn.inst zero) =
        (le zero N ⟶ (β * ap2 (sumF (kB t)) (succ zero) x ≐ α * ap2 (sumF t) zero x)) := by
      simp
    rw [e]
    exact .impI (shift_base t α β x)
  · have e : (le (var 0) (Syn.shift N) ⟶
          (Syn.shift β * ap2 (sumF (kB t)) (succ (var 0)) (Syn.shift x) ≐
            Syn.shift α * ap2 (sumF t) (var 0) (Syn.shift x))).subst (Syn.repl (succ (var 0))) =
        (le (succ (var 0)) (Syn.shift N) ⟶
          (Syn.shift β * ap2 (sumF (kB t)) (succ (succ (var 0))) (Syn.shift x) ≐
            Syn.shift α * ap2 (sumF t) (succ (var 0)) (Syn.shift x))) := by
      simp
    rw [e]
    exact .impI (shift_guard t Prf.hyp0 hr.allOpen.wk.wk Prf.hyp1)

/-- `prop:poisson`, the finite stage: weights with `(k + 1) β t(k + 1) = α t(k)` for `k < N` satisfy
`β ∑_{k<N+1} k t(k) = α ∑_{j<N} t(j)`. -/
theorem shift_identity {α β N x : PTm n}
    (hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (succ (var 0) * (Syn.shift β * inst2 t (succ (var 0)) (Syn.shift x)) ≐
        Syn.shift α * inst2 t (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] β * ap2 (sumF (kB t)) (succ N) x ≐ α * ap2 (sumF t) N x := by
  have a := Prf.allE N (shift_all t hr)
  have e : (le (var 0) (Syn.shift N) ⟶
        (Syn.shift β * ap2 (sumF (kB t)) (succ (var 0)) (Syn.shift x) ≐
          Syn.shift α * ap2 (sumF t) (var 0) (Syn.shift x))).subst (Syn.inst N) =
      (le N N ⟶ (β * ap2 (sumF (kB t)) (succ N) x ≐ α * ap2 (sumF t) N x)) := by
    simp
  rw [e] at a
  exact Prf.impE a (le_refl N)

end Abstract

/-! ## The Poisson weights -/

/-- `(k + 1) · M!/(k + 1)! = M!/k!` for `k < M`, with `M!/k! = (M)_{M−k}`. -/
theorem ff_ratio {k M : PTm n} (h : Γ ⊢[PRAAx] lt k M) :
    Γ ⊢[PRAAx] succ k * ff M (monus M (succ k)) ≐ ff M (monus M k) := by
  have h' : Γ ⊢[PRAAx] le (succ k) M := h
  have a₁ := natEq (ff_fact_k h')
  have a₀ := natEq (ff_fact_k (le_of_lt h))
  have f := natEq (fact_succ (Γ := Γ) k zero)
  refine mul_cancel (fact_pos k) ?_
  apply deriveNat; ipra_simps
  linear_combination a₁ - a₀ - 𝔟(ff M (monus M (succ k))) * f

theorem monus_pred {k M : PTm n} (h : Γ ⊢[PRAAx] lt k M) :
    Γ ⊢[PRAAx] monus M k ≐ succ (monus M (succ k)) := by
  have h' : Γ ⊢[PRAAx] le (succ k) M := h
  have k₁ := natEq (eq_add_of_le h')
  have k₀ := natEq (eq_add_of_le (le_of_lt h))
  apply deriveNat; ipra_simps
  linear_combination k₁ - k₀

/-- The ratio recurrence of `t(k) = a^k b^{M−k} M!/k!`: `(k + 1) b t(k + 1) = a t(k)` for `k < M`. -/
theorem po_ratio {k M a b : PTm n} (h : Γ ⊢[PRAAx] lt k M) :
    Γ ⊢[PRAAx] succ k * (b * (pw a (succ k) * pw b (monus M (succ k)) * ff M (monus M (succ k)))) ≐
      a * (pw a k * pw b (monus M k) * ff M (monus M k)) := by
  have pa := natEq (pw_succ (Γ := Γ) a k)
  have pb := natEq ((congrAp2 powF (monus_pred h) (.eqRefl b)).eqTrans (pw_succ (Γ := Γ) b (monus M (succ k))))
  have fr := natEq (ff_ratio h)
  apply deriveNat; ipra_simps
  linear_combination (𝔟 k + 1) * 𝔟 b * 𝔟(pw b (monus M (succ k))) * 𝔟(ff M (monus M (succ k))) * pa -
    𝔟 a * 𝔟(pw a k) * 𝔟(ff M (monus M k)) * pb +
    𝔟 a * 𝔟(pw a k) * 𝔟(pw b (monus M (succ k))) * 𝔟 b * fr

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
