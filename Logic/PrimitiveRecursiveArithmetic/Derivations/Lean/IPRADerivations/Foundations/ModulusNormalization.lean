import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Foundations.ReverseDemand

/-!
# Normalizing a modulus to a monotone one

Packets:

* `foundations/ipra_framework_2026-11-15`, `framework.tex`, the remark "Correction to the convenient
  precision-index form" after the lemma "Algebra of dyadic Cauchy names": "Replace each modulus `μ` by
  `μ̂(k) = max_{i ≤ k} μ(i) + k`, which is PR and monotone. Then both approximants at precision `k, l ≥ k` lie
  beyond `μ(k + 2)`";
* `analysis/calculus_ipra`, `report.tex`, `eq:munormal`: `μ(k) = k + max_{i ≤ k} μ_old(i)`.

For a modulus `μ(i, x)` with parameter `x` and the running maximum `Mx` of `Probability/UnionUtility`:

* `mhat μ k x = k + max_{i ≤ k} μ(i, x)`;
* `index_le`: `k ≤ μ̂(k)`;
* `modulus_le`: `μ(i) ≤ μ̂(k)` for `i ≤ k`; in particular every later normalized index lies beyond the
  original modulus at an earlier precision;
* `mx_mono`, `mhat_mono`: the running maximum and `μ̂` are monotone.

The monotonicity of the running maximum uses its argmax: the maximum over `i ≤ k` is attained at some
`i ≤ k ≤ l`.

Also the pair case of `thm:mod` ("Composition of observation moduli") of
`foundations/ipra_uniformity_framework_2026-11-15`: the pair of two names, with the sup metric, has the
modulus `max(M_q, M_r)`.

* `pair_modulus`: if the first distance is at most `e` beyond the index `M_q` and the second beyond `M_r`,
  then beyond `max(M_q, M_r)` the maximum of the two distances is at most `e`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ModulusNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.UnionUtility (Mx Ag mx_upper ag_attains)
open LeanProofs.IPRA.Probability.Ninther (mx)
open LeanProofs.IPRA.Foundations.ReverseDemand (le_mx_left le_mx_right mx_lub)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)} (μ : PTm 2)

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `μ̂(k, x) = k + max_{i ≤ k} μ(i, x)`. -/
abbrev mhat (k x : PTm n) : PTm n := k + Mx μ (succ k) x

/-- `k ≤ μ̂(k)`. -/
theorem index_le (k x : PTm n) : Γ ⊢[PRAAx] le k (mhat μ k x) := by
  ipra_le 𝔟 (Mx μ (succ k) x)

/-- `μ(i) ≤ μ̂(k)` for `i ≤ k`. -/
theorem modulus_le {i k x : PTm n} (h : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx] le (inst2 μ i x) (mhat μ k x) := by
  have g : Γ ⊢[PRAAx] le (succ i) (succ k) := by ipra_le sl h
  have u := mx_upper μ (b := i) (K := succ k) (x := x) g
  ipra_le sl u + 𝔟 k

/-- The running maximum is monotone in its length. -/
theorem mx_mono {k l x : PTm n} (h : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] le (Mx μ (succ k) x) (Mx μ (succ l) x) := by
  have a := ag_attains μ (Γ := Γ) k x
  have a₁ : Γ ⊢[PRAAx] le (succ (Ag μ (succ k) x)) (succ k) := Prf.andE₁ a
  have g : Γ ⊢[PRAAx] le (succ (Ag μ (succ k) x)) (succ l) := by ipra_le sl a₁ + sl h
  exact le_congr (Prf.andE₂ a) (.eqRefl _) (mx_upper μ (b := Ag μ (succ k) x) (K := succ l) (x := x) g)

/-- `μ̂` is monotone. -/
theorem mhat_mono {k l x : PTm n} (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (mhat μ k x) (mhat μ l x) := by
  have m := mx_mono μ (x := x) h
  ipra_le sl h + sl m

/-! ## The pair of two names -/

/-- `thm:mod`, the pair: beyond `max(M_q, M_r)` both distances, hence their maximum, are at most `e`. -/
theorem pair_modulus {Mq Mr m dq dr e : PTm n} (hq : Γ ⊢[PRAAx] le Mq m ⟶ le dq e)
    (hr : Γ ⊢[PRAAx] le Mr m ⟶ le dr e) (hm : Γ ⊢[PRAAx] le (mx Mq Mr) m) :
    Γ ⊢[PRAAx] le (mx dq dr) e :=
  mx_lub (Prf.impE hq (le_trans (le_mx_left Mq Mr) hm)) (Prf.impE hr (le_trans (le_mx_right Mq Mr) hm))

end LeanProofs.IPRA.Foundations.ModulusNormalization
