import IPRADerivations.Analysis.SpecialFunctions.HypergeometricRatio
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Parity
import IPRADerivations.Core.LinearCombination

/-!
# An explicit ratio threshold for hypergeometric terms

Packet: `analysis/meijer_g_ipra_2026-11-16`, `paper/sections/03_hypergeometric_engine.tex`, Theorem `thm:hyp-conv`
("Primitive-recursive convergence"), case (a): "if `r ≤ s`, then for every bounded `w` a primitive-recursive search
produces `N` and `ρ = 1/2` satisfying `eq:ratio-majorant`". Its proof: "the desired ratio inequality is a polynomial
inequality in `k`. In case (a) the denominator has strictly larger degree … A coarse explicit threshold is obtained
by replacing every `k + M_i` by `(1 + M) k`".

For natural parameter lists `as`, `bs` with `|as| ≤ |bs|` and the terms `T_k = Num_k / Den_k` of
`HypergeometricRatio` (`Num_k = z^k ∏ (a_i)_k`, `Den_k = k! ∏ (b_j)_k`), no search is needed; the threshold is
explicit:

* `pair_le`: `a + k ≤ (1 + a)(b + k)` for `k ≥ 1`;
* `shift_le`: `∏_i (a_i + k) ≤ ∏_i (1 + a_i) · ∏_j (b_j + k)` for `k ≥ 1`, pairing the parameters;
* `half_ratio`: if `k ≥ 1` and `2 z ∏_i (1 + a_i) ≤ k + 1`, then `2 T_{k+1} ≤ T_k`, i.e.
  `2 Num_{k+1} Den_k ≤ Num_k Den_{k+1}` — the ratio bound with `ρ = 1/2` for every `k ≥ N = 2 z ∏ (1 + a_i)`.

It follows from the exact term ratio `pfq_ratio` after cancelling `z ∏ (a_i + k)` (or, if that factor vanishes,
because `T_{k+1} = 0`). Signed or rational parameters and case (b) are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.HypergeometricThreshold

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.HypergeometricRatio (prodL pochL shiftL pochL_succ Num Den pfq_ratio)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `a + k ≤ (1 + a)(b + k)` for `k ≥ 1`. -/
theorem pair_le (a b : PTm n) {k : PTm n} (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le (a + k) ((one + a) * (b + k)) := by
  refine le_of_eq_add (d := b + a * b + a * monus k one) ?_
  ipra_lc Groth.ι (Q.mk Γ a) * natEq (eq_add_of_le hk)

/-- `1 ≤ ∏_j (b_j + k)` for `k ≥ 1`. -/
theorem one_le_shift (bs : List (PTm n)) {k : PTm n} (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le one (shiftL bs k) := by
  induction bs with
  | nil => exact le_refl one
  | cons b l ih =>
    have h1 : Γ ⊢[PRAAx] le one (b + k) :=
      le_trans hk (le_congr (.eqRefl _) (add_comm k b) (le_add_right k b))
    have h2 : Γ ⊢[PRAAx] le (one * one) ((b + k) * shiftL l k) := le_mul_mono h1 ih
    exact le_congr (one_mul one) (.eqRefl _) h2

/-- `∏_i (a_i + k) ≤ ∏_i (1 + a_i) · ∏_j (b_j + k)` for `k ≥ 1` and `|as| ≤ |bs|`. -/
theorem shift_le (as : List (PTm n)) {k : PTm n} (hk : Γ ⊢[PRAAx] le one k) :
    ∀ bs : List (PTm n), as.length ≤ bs.length →
      (Γ ⊢[PRAAx] le (shiftL as k) (prodL (as.map fun a => one + a) * shiftL bs k)) := by
  induction as with
  | nil =>
    intro bs _
    have h : Γ ⊢[PRAAx] le one (one * shiftL bs k) :=
      le_congr (.eqRefl _) (one_mul _).eqSymm (one_le_shift bs hk)
    exact h
  | cons a l ih =>
    intro bs hlen
    cases bs with
    | nil => exact absurd hlen (by simp)
    | cons b bs' =>
      have ih' := ih bs' (Nat.le_of_succ_le_succ hlen)
      have h : Γ ⊢[PRAAx] le ((a + k) * shiftL l k)
          (((one + a) * (b + k)) * (prodL (l.map fun a => one + a) * shiftL bs' k)) :=
        le_mul_mono (pair_le a b hk) ih'
      have h' : Γ ⊢[PRAAx] le ((a + k) * shiftL l k)
          (((one + a) * prodL (l.map fun a => one + a)) * ((b + k) * shiftL bs' k)) :=
        le_congr (.eqRefl _) (by ipra_ring) h
      exact h'

/-- From `S X = u Y` and `S = 2u + D`: `u Y = u (2X) + D X`. -/
theorem cancel_alg {S X Y u D : PTm n} (pf : Γ ⊢[PRAAx] S * X ≐ u * Y) (e : Γ ⊢[PRAAx] S ≐ two * u + D) :
    Γ ⊢[PRAAx] u * Y ≐ u * (two * X) + D * X := by
  have p' := natEq pf
  have e' := natEq e
  apply deriveNat; ipra_simps
  linear_combination (-1 : Groth (Q Γ)) * p' + Groth.ι (Q.mk Γ X) * e'

/-- `thm:hyp-conv` (a) with an explicit threshold: for `|as| ≤ |bs|`, `k ≥ 1` and `2 z ∏ (1 + a_i) ≤ k + 1`,
`2 T_{k+1} ≤ T_k`. -/
theorem half_ratio (as bs : List (PTm n)) (hlen : as.length ≤ bs.length) {z k : PTm n}
    (hk : Γ ⊢[PRAAx] le one k)
    (hN : Γ ⊢[PRAAx] le (two * z * prodL (as.map fun a => one + a)) (succ k)) :
    Γ ⊢[PRAAx] le (two * (Num as z (succ k) * Den bs k)) (Num as z k * Den bs (succ k)) := by
  have hS := shift_le as hk bs hlen
  -- `2 (z ∏ (a_i + k)) ≤ (k + 1) ∏ (b_j + k)`
  have H : Γ ⊢[PRAAx] le (two * (z * shiftL as k)) (succ k * shiftL bs k) := by
    have h1 := le_mul_mono (le_refl (two * z)) hS
    have h2 := le_mul_mono hN (le_refl (shiftL bs k))
    exact le_trans (le_congr (by ipra_ring) (by ipra_ring) h1) h2
  have pf := pfq_ratio (Γ := Γ) as bs z k
  refine .orE (zero_or_succ (z * shiftL as k)) ?_ ?_
  · -- the factor vanishes: `T_{k+1} = 0`
    have hz : ((z * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] z * shiftL as k ≐ zero := Prf.hyp0
    have nE : ((z * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] Num as z (succ k) ≐
        (pw z k * z) * (pochL as k * shiftL as k) := congrMul (pw_succ z k) (pochL_succ as k)
    have re : ((z * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] (pw z k * z) * (pochL as k * shiftL as k) ≐
        (pw z k * pochL as k) * (z * shiftL as k) := by ipra_ring
    have n0 := nE.eqTrans (re.eqTrans ((congrMul (.eqRefl _) hz).eqTrans (mul_zero _)))
    have x0 : ((z * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] two * (Num as z (succ k) * Den bs k) ≐ zero :=
      (congrMul (.eqRefl _) ((congrMul n0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
    exact le_congr x0.eqSymm (.eqRefl _) (zero_le _)
  · -- cancel the positive factor `z ∏ (a_i + k)`
    have hpos : ((z * shiftL as k ≐ succ (pred (z * shiftL as k))) :: Γ) ⊢[PRAAx]
        z * shiftL as k ≐ succ (pred (z * shiftL as k)) := Prf.hyp0
    have c := cancel_alg (pf.wk (ψ := z * shiftL as k ≐ succ (pred (z * shiftL as k))))
      (eq_add_of_le (H.wk (ψ := z * shiftL as k ≐ succ (pred (z * shiftL as k)))))
    have hle := le_of_eq_add c
    exact mul_le_cancel (le_congr (congrMul hpos (.eqRefl _)) (congrMul hpos (.eqRefl _)) hle)

end LeanProofs.IPRA.Analysis.HypergeometricThreshold
