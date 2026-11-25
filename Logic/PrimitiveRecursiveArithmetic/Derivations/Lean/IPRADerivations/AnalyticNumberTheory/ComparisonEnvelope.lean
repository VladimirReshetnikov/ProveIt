import IPRADerivations.AnalyticNumberTheory.SelbergComparison
import IPRADerivations.AnalyticNumberTheory.FourthRootSum
import IPRADerivations.Core.CommonLemmas

/-!
# The fourth-root envelope of the comparison error (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"For each `d ≤ x`, apply (sb:comparison-error) at `y = x/d` … The preceding integral bound gives
`log z + 1 ≤ 4z^{1/4}` for `z ≥ 1`." This module bounds the two error budgets of
`SelbergComparison.comparison_upper/lower` at a point `y` by the fourth-root envelope, with `r = ⌊√⌊√y⌋⌋`,
`R = r + 1`, `F = L!`:

* `harm_one`: `H_X ≤ λ_K(X) + 1`, i.e. `S(X) + S(K) ≤ S(KX) + F` (so also `c ≤ 1`);
* `lam_succ`: `λ_K(r + 1) ≤ r` (`log(1 + r) ≤ r`);
* `lam_fourth`: `λ_K(y) ≤ 4r + 3` (`log y ≤ 4 log R`, by subadditivity twice, `y < R⁴`);
* `env_upper`: `19mFu + 22mFC + Fu + (u + 2C)S(y) + 2F S(y) ≤ 142 F² R³`;
* `env_lower`: `Fu + 2u S(y) + 19mFu + 16mFC + 2F S(y) ≤ 146 F² R³`.

With `FourthRootSum.fourth_root_sum` (`Σ_d R_d³ ≤ 15x`) the summed comparison error over `d ≤ x` is at most
`146 · 15 F² x`. The final certificates were found by exact polynomial residuals.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale subadd)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U S_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorBound (eta_bounds)
open LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel (CT quo_one' c_nonneg)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergComparison (c16 c19 c22)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (qr Q4 Q4_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (quo_le_self)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

alias le_mul2 := Common.mul_le_mul

/-- `H_X ≤ λ_K(X) + 1`: `S(X) + S(K) ≤ S(KX) + F` for `K, X ≥ 1`, `KX ≤ L`. -/
theorem harm_one {K X L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hX : Γ ⊢[PRAAx] le one X)
    (hL : Γ ⊢[PRAAx] le (K * X) L) :
    Γ ⊢[PRAAx] le (S X (fact L) + S K (fact L)) (S (K * X) (fact L) + fact L) := by
  have c1 := Prf.andE₁ (eta_bounds (m := one) (le_refl _) hX hK hL)
  have q1 : Γ ⊢[PRAAx] K * one ≐ K := by ipra_ring
  have eK1 := natEq (congrAp2 (Γ := Γ) (sumF hB) q1 (.eqRefl (fact L)))
  have eSs := natEq (S_succ (Γ := Γ) zero (fact L))
  have eS0 := natEq (sum_zero (Γ := Γ) hB (fact L))
  have eq1 := natEq (quo_one' (Γ := Γ) (fact L))
  ipra_le sl c1 with -eK1 + eSs + eS0 + eq1

/-- `λ_K(r + 1) ≤ r`: `S(K(r+1)) ≤ S(K) + rF`. -/
theorem lam_succ {K : PTm n} (r F : PTm n) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] le (S (K * succ r) F) (S K F + r * F) := by
  have lu := log_upper (Γ := Γ) K (K * r) F
  have q : Γ ⊢[PRAAx] K * succ r ≐ K + K * r := by ipra_ring
  have e := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl F))
  have wK := natEq hK
  refine mul_le_cancel (d' := K) ?_
  ipra_le sl lu + 𝔞 r * 𝔞 F with (𝔞 K + 1) * e

/-- `y ≤ (qr(y) + 1)⁴`. -/
theorem y_le_Q4 (y : PTm n) : Γ ⊢[PRAAx] le y (Q4 (qr y)) := by
  have a := lt_isqrt_succ_sq (Γ := Γ) y
  have b := lt_isqrt_succ_sq (Γ := Γ) (isqrt y)
  have b' : Γ ⊢[PRAAx] le (succ (isqrt y)) (succ (qr y) * succ (qr y)) :=
    le_congr (.eqRefl _) (by ipra_ring) b
  have c := sq_le_sq b'
  have a' : Γ ⊢[PRAAx] le (succ y) (succ (isqrt y) * succ (isqrt y)) :=
    le_congr (.eqRefl _) (by ipra_ring) a
  exact le_trans (le_succ_self _) (le_trans a' c)

/-- `λ_K(y) ≤ 4r + 3` for `r = qr(y)`: `S(Ky) ≤ S(K) + 4rF + 3F`, for `K ≥ 1`, `K (r+1)⁴ ≤ L`. -/
theorem lam_fourth {y K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * Q4 (qr y)) L) :
    Γ ⊢[PRAAx] le (S (K * y) (fact L)) (S K (fact L) + two * (two * (qr y * fact L)) + succ two * fact L) := by
  have hKp := pos_of_lt_zero hK
  have hR : Γ ⊢[PRAAx] succ (qr y) ≐ succ (pred (succ (qr y))) := congrSucc (pred_succ _).eqSymm
  have hRR : Γ ⊢[PRAAx] succ (qr y) * succ (qr y) ≐ succ (pred (succ (qr y) * succ (qr y))) :=
    FloorTelescope.sq_pos (qr y)
  have mono := S_mono (fact L) (le_scale K (y_le_Q4 (Γ := Γ) y))
  have s2 := subadd (M := K) hKp hRR hRR hL
  have hL2 : Γ ⊢[PRAAx] le (K * (succ (qr y) * succ (qr y))) L := by
    refine le_trans (le_of_eq_add (d := K * (succ (qr y) * succ (qr y)) *
      (qr y * qr y + two * qr y)) (by ipra_ring)) hL
  have s1 := subadd (M := K) hKp hR hR hL2
  have ls := lam_succ (Γ := Γ) (qr y) (fact L) hKp
  have qK := le_congr (congrAp2 quoF (.eqRefl _) hKp).eqSymm (.eqRefl _) (quo_le_self (pred K) (fact L))
  ipra_le sl mono + sl s2 + 2 * sl s1 + 4 * sl ls + 3 * sl qK

/-- The upper comparison budget at `y` is at most `142 F² R³`. -/
theorem env_upper {y K L X : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hy : Γ ⊢[PRAAx] le one y)
    (hX : Γ ⊢[PRAAx] le one X) (hLX : Γ ⊢[PRAAx] le (K * X) L) (hL4 : Γ ⊢[PRAAx] le (K * Q4 (qr y)) L) :
    Γ ⊢[PRAAx] le (c19 (isqrt y * (fact L * U y K (fact L))) + c22 (isqrt y * (fact L * CT K X (fact L))) +
        fact L * U y K (fact L) + (U y K (fact L) + two * CT K X (fact L)) * S y (fact L) +
        two * (fact L * S y (fact L)))
      (num 142 * (fact L * fact L * (succ (qr y) * succ (qr y) * succ (qr y)))) := by
  have hKy : Γ ⊢[PRAAx] le (K * y) L := le_trans (le_scale K (y_le_Q4 (Γ := Γ) y)) hL4
  have hu0 := lam_fourth (y := y) hK hL4
  have m1 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * y) (fact L)) :=
    S_mono (fact L) (le_trans (by have t := le_scale K hy; ipra_le sl t) (le_refl _))
  have Eu := natEq (eq_add_of_le m1)
  have hu : Γ ⊢[PRAAx] le (U y K (fact L)) (two * (two * (qr y * fact L)) + succ two * fact L) := by
    ipra_le sl hu0 with -Eu
  have hS0 : Γ ⊢[PRAAx] le (S y (fact L)) (U y K (fact L) + fact L) := by
    have h := harm_one hK hy hKy; ipra_le sl h with Eu
  have EC := natEq (eq_add_of_le (c_nonneg hK hX hLX))
  have hC : Γ ⊢[PRAAx] le (CT K X (fact L)) (fact L) := by
    have h := harm_one hK hX hLX; ipra_le sl h with -EC
  have hm : Γ ⊢[PRAAx] le (isqrt y) (succ (qr y) * succ (qr y)) :=
    le_trans (le_succ_self _) (le_congr (.eqRefl _) (by ipra_ring)
      (lt_isqrt_succ_sq (isqrt y)))
  have bu : Γ ⊢[PRAAx] le (U y K (fact L)) (two * two * (fact L * succ (qr y))) := by
    ipra_le sl hu + 𝔞 (fact L)
  have bS : Γ ⊢[PRAAx] le (S y (fact L)) (succ (two * two) * (fact L * succ (qr y))) := by
    ipra_le sl hS0 + sl bu + 𝔞 (fact L) * 𝔞 (qr y)
  have bC : Γ ⊢[PRAAx] le (CT K X (fact L)) (fact L * succ (qr y)) := by
    ipra_le sl hC + 𝔞 (fact L) * 𝔞 (qr y)
  have p1 := le_mul2 hm (le_scale (fact L) bu)
  have p2 := le_mul2 hm (le_scale (fact L) bC)
  have p3 := le_scale (fact L) bu
  have b6 : Γ ⊢[PRAAx] le (U y K (fact L) + two * CT K X (fact L))
      (two * two * (fact L * succ (qr y)) + two * (fact L * succ (qr y))) := by
    ipra_le sl bu + 2 * sl bC
  have p4 := le_mul2 b6 bS
  have p5 := le_scale (fact L) bS
  ipra_le 19 * sl p1 + 22 * sl p2 + sl p3 + sl p4 + 2 * sl p5 +
    𝔞 (fact L) * 𝔞 (fact L) * (𝔞 (qr y) + 1) * (44 * 𝔞 (qr y) * 𝔞 (qr y) + 58 * 𝔞 (qr y))

/-- The lower comparison budget at `y` is at most `146 F² R³`. -/
theorem env_lower {y K L X : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hy : Γ ⊢[PRAAx] le one y)
    (hX : Γ ⊢[PRAAx] le one X) (hLX : Γ ⊢[PRAAx] le (K * X) L) (hL4 : Γ ⊢[PRAAx] le (K * Q4 (qr y)) L) :
    Γ ⊢[PRAAx] le (fact L * U y K (fact L) + two * (U y K (fact L) * S y (fact L)) +
        c19 (isqrt y * (fact L * U y K (fact L))) + c16 (isqrt y * (fact L * CT K X (fact L))) +
        two * (fact L * S y (fact L)))
      (num 146 * (fact L * fact L * (succ (qr y) * succ (qr y) * succ (qr y)))) := by
  have hKy : Γ ⊢[PRAAx] le (K * y) L := le_trans (le_scale K (y_le_Q4 (Γ := Γ) y)) hL4
  have hu0 := lam_fourth (y := y) hK hL4
  have m1 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * y) (fact L)) :=
    S_mono (fact L) (le_trans (by have t := le_scale K hy; ipra_le sl t) (le_refl _))
  have Eu := natEq (eq_add_of_le m1)
  have hu : Γ ⊢[PRAAx] le (U y K (fact L)) (two * (two * (qr y * fact L)) + succ two * fact L) := by
    ipra_le sl hu0 with -Eu
  have hS0 : Γ ⊢[PRAAx] le (S y (fact L)) (U y K (fact L) + fact L) := by
    have h := harm_one hK hy hKy; ipra_le sl h with Eu
  have EC := natEq (eq_add_of_le (c_nonneg hK hX hLX))
  have hC : Γ ⊢[PRAAx] le (CT K X (fact L)) (fact L) := by
    have h := harm_one hK hX hLX; ipra_le sl h with -EC
  have hm : Γ ⊢[PRAAx] le (isqrt y) (succ (qr y) * succ (qr y)) :=
    le_trans (le_succ_self _) (le_congr (.eqRefl _) (by ipra_ring)
      (lt_isqrt_succ_sq (isqrt y)))
  have bu : Γ ⊢[PRAAx] le (U y K (fact L)) (two * two * (fact L * succ (qr y))) := by
    ipra_le sl hu + 𝔞 (fact L)
  have bS : Γ ⊢[PRAAx] le (S y (fact L)) (succ (two * two) * (fact L * succ (qr y))) := by
    ipra_le sl hS0 + sl bu + 𝔞 (fact L) * 𝔞 (qr y)
  have bC : Γ ⊢[PRAAx] le (CT K X (fact L)) (fact L * succ (qr y)) := by
    ipra_le sl hC + 𝔞 (fact L) * 𝔞 (qr y)
  have p1 := le_mul2 hm (le_scale (fact L) bu)
  have p2 := le_mul2 hm (le_scale (fact L) bC)
  have p3 := le_scale (fact L) bu
  have p4 := le_mul2 bu bS
  have p5 := le_scale (fact L) bS
  ipra_le sl p3 + 2 * sl p4 + 19 * sl p1 + 16 * sl p2 + 2 * sl p5 +
    𝔞 (fact L) * 𝔞 (fact L) * (𝔞 (qr y) + 1) * (54 * 𝔞 (qr y) * 𝔞 (qr y) + 68 * 𝔞 (qr y))

end LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope
