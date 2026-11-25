import IPRADerivations.Algebra.PowerDifference
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.CertificateTactics

/-!
# Dyadic arithmetic of the analytic moduli

Packets: `analytic-number-theory/pnt_li_ipra_2026-11-15` (the integer arithmetic in the proof of
`thm:theta-modulus-established`) and `analytic-number-theory/zeta_ipra_proof_package`
(`lem:d-tail`, the geometric majorant).

* `modulus_exponent`: `2^100 (2^14 (r + 1))^10 = 2^240 (r + 1)^10`, the identity that turns the
  hypothesis `n ≥ 2^(C (r+1)^10)`, `C = 2^240`, into `k ≥ 2^14 (r + 1)`;
* `floor_bound`: `8 (r + 1) ≤ k`, `k = 8q + ρ`, `ρ < 8` give `r + 1 ≤ q`, i.e.
  `r + 1 ≤ ⌊k/8⌋`;
* `dyadic_rate`: `r + 1 ≤ q` gives `2 · 2^r ≤ 2^q`, the cleared form of `2 · 2^(−q) ≤ 2^(−r)`;
* `theta_rate`: the two steps combined;
* `geom_two`: `1 + ∑_{j<R} 2^j = 2^R`, so `∑_{j<R} 2^(−j) < 2`: any finite collection of groups
  of the dyadic tail is bounded by twice the first group.

The divergence side of (D2), a block `2^(a−1) < n ≤ 2^a` contributing at least `1/2` at
`σ = 1`, is `AnalyticNumberTheory/Harmonic`. The analytic estimates themselves are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DyadicModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.PowerDifference (gd geom_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `2^100 (2^14 (r + 1))^10 = 2^240 (r + 1)^10`. -/
theorem modulus_exponent (r : PTm n) :
    Γ ⊢[PRAAx] pw two (num 100) * pw (pw two (num 14) * succ r) (num 10) ≐
      pw two (num 240) * pw (succ r) (num 10) := by
  have e₁ : Γ ⊢[PRAAx] (num 14 * num 10 : PTm n) ≐ num 140 := by
    apply deriveNat; ipra_simps; norm_num
  have e₂ : Γ ⊢[PRAAx] (num 100 + num 140 : PTm n) ≐ num 240 := by
    apply deriveNat; ipra_simps; norm_num
  ipra_lc 𝔞(pw two (num 100)) * natEq (pw_mul_base (Γ := Γ) (pw two (num 14)) (succ r) (num 10)) +
    𝔞(pw two (num 100)) * 𝔞(pw (succ r) (num 10)) * natEq ((pw_mul (Γ := Γ) two (num 14) (num 10)).eqTrans (congrAp2 powF e₁ (.eqRefl two))) -
    𝔞(pw (succ r) (num 10)) * natEq ((congrAp2 powF e₂.eqSymm (.eqRefl (two : PTm n))).eqTrans (pw_add (Γ := Γ) two (num 100) (num 140)))

/-- `8 (r + 1) ≤ k = 8q + ρ` with `ρ < 8` gives `r + 1 ≤ q`. -/
theorem floor_bound {r q ρ k : PTm n} (hk : Γ ⊢[PRAAx] le (num 8 * succ r) k)
    (hd : Γ ⊢[PRAAx] k ≐ num 8 * q + ρ) (hρ : Γ ⊢[PRAAx] lt ρ (num 8)) : Γ ⊢[PRAAx] le (succ r) q := by
  refine .orE (lt_or_le q (succ r)) ?_ Prf.hyp0
  have hk' : (lt q (succ r) :: Γ) ⊢[PRAAx] le (num 8 * succ r) k := hk.wk
  have hd' : (lt q (succ r) :: Γ) ⊢[PRAAx] k ≐ num 8 * q + ρ := hd.wk
  have hρ' : (lt q (succ r) :: Γ) ⊢[PRAAx] lt ρ (num 8) := hρ.wk
  have big : (lt q (succ r) :: Γ) ⊢[PRAAx] le (succ k) (num 8 * succ r) := by
    refine le_of_eq_add (d := monus (num 8) (succ ρ) + num 8 * monus (succ r) (succ q)) ?_
    ipra_lc 8 * natEq (eq_add_of_le (Prf.hyp0 : (lt q (succ r) :: Γ) ⊢[PRAAx] le (succ q) (succ r))) - natEq hd' +
      natEq (eq_add_of_le hρ')
  exact not_succ_le_self k _ (le_trans big hk')

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_eq_succ (.eqRefl _)

/-- `r + 1 ≤ q` gives `2 · 2^r ≤ 2^q`. -/
theorem dyadic_rate {r q : PTm n} (h : Γ ⊢[PRAAx] le (succ r) q) :
    Γ ⊢[PRAAx] le (two * pw two r) (pw two q) :=
  le_congr ((pw_succ two r).eqTrans (mul_comm _ _)) (.eqRefl _) (pw_le_exp two_pos h)

/-- From `8 (r + 1) ≤ k`: `2 · 2^r ≤ 2^⌊k/8⌋`, the last step of `thm:theta-modulus-established`. -/
theorem theta_rate {r q ρ k : PTm n} (hk : Γ ⊢[PRAAx] le (num 8 * succ r) k)
    (hd : Γ ⊢[PRAAx] k ≐ num 8 * q + ρ) (hρ : Γ ⊢[PRAAx] lt ρ (num 8)) :
    Γ ⊢[PRAAx] le (two * pw two r) (pw two q) := dyadic_rate (floor_bound hk hd hρ)

/-- `1 + ∑_{j<R} 2^j = 2^R`. -/
theorem geom_two (R : PTm n) : Γ ⊢[PRAAx] succ (gd two one R) ≐ pw two R := by
  refine add_right_cancel (c := gd two one R) ?_
  ipra_lc -natEq (geom_sum (Γ := Γ) two R)

end LeanProofs.IPRA.AnalyticNumberTheory.DyadicModulus
