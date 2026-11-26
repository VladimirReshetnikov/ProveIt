import IPRADerivations.Foundations.ClockMajorants
import IPRADerivations.Core.Header

/-!
# The exponential clock of the diagonal language

Packet: `foundations/ipra_complexity_foundations_2026-11-20`, `tex/diagonal.tex`, Lemma `lem:diagonal-exp` ("a
fixed deterministic machine computes `D(w)` in at most `2^{K(|w|+1)^2}` transitions"), its two arithmetic steps:

* `clock_exp` (`eq:diag-clock-bound`): for recovered constants `c ≤ n`, `k ≤ n`, the countdown length
  `T = c(n+1)^k` satisfies `T ≤ n(n+1)^n ≤ 2^n 2^{n²} = 2^{n²+n} ≤ 2^{(n+1)²}`;
* `cost_exp`: with `q ≥ 1` and `n + T + 1 ≤ 2^{q+1}` (both `T` and `n + 1` are at most `2^q`),
  `A (n + T + 1)^4 ≤ 16 A 2^{4q} ≤ 2^{(4 + 16A) q}`, the paper's constant "`K = 4 + 16A` works".
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DiagonalClock

open_ipra
open LeanProofs.IPRA.Foundations.ClockMajorants (pw_mono_exp)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (pw_num)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `eq:diag-clock-bound`: `c(n+1)^k ≤ 2^{(n+1)²}` for `c, k ≤ n`. -/
theorem clock_exp {c k m : PTm n} (hc : Γ ⊢[PRAAx] le c m) (hk : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] le (c * pw (succ m) k) (pw two (succ m * succ m)) := by
  have hN : Γ ⊢[PRAAx] le one (succ m) := by ipra_le 𝔟 m
  have h2 : Γ ⊢[PRAAx] le one two := by ipra_le 1
  have a1 := pw_mono_exp hN hk
  have a2 : Γ ⊢[PRAAx] le (pw (succ m) m) (pw two (m * m)) :=
    le_congr (.eqRefl _) (pw_mul _ _ _) (pw_le_pw m (succ_le_two_pow m))
  have a12 := le_trans a1 a2
  have p := succ_le_two_pow (Γ := Γ) m
  have a3 : Γ ⊢[PRAAx] le c (pw two m) := le_trans hc (by ipra_le sl p + 1)
  have a4 : Γ ⊢[PRAAx] le (c * pw (succ m) k) (pw two m * pw two (m * m)) := by
    ipra_le sl a3 * 𝔟 (pw two (m * m)) + 𝔟 c * sl a12
  have a6 : Γ ⊢[PRAAx] le (pw two (m + m * m)) (pw two (succ m * succ m)) :=
    pw_mono_exp h2 (by ipra_le 𝔟 m + 1)
  exact le_trans (le_congr (.eqRefl _) (pw_add _ _ _).eqSymm a4) a6

/-- `A (n + T + 1)^4 ≤ 2^{(4 + 16A) q}` when `n + T + 1 ≤ 2^{q+1}`, `q ≥ 1`. -/
theorem cost_exp {A X q : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hX : Γ ⊢[PRAAx] le X (pw two (succ q))) :
    Γ ⊢[PRAAx] le (A * pw X (num 4)) (pw two ((num 4 + num 16 * A) * q)) := by
  have h2 : Γ ⊢[PRAAx] le one two := by ipra_le 1
  have s1 : Γ ⊢[PRAAx] le (pw X (num 4)) (pw two (succ q * num 4)) :=
    le_congr (.eqRefl _) (pw_mul _ _ _) (pw_le_pw (num 4) hX)
  have e4 := natEq ((congrAp2 (Γ := Γ) powF (show Γ ⊢[PRAAx] succ q * num 4 ≐ num 4 + num 4 * q by
    ipra_ring) (.eqRefl two)).eqTrans (pw_add _ _ _))
  have e16 := natEq (show Γ ⊢[PRAAx] pw two (num 4) ≐ num 16 from pw_num 2 4)
  have u1 : Γ ⊢[PRAAx] le (A * pw X (num 4)) (num 16 * A * pw two (num 4 * q)) := by
    ipra_le 𝔟 A * sl s1 with -𝔟 A * e4 - 𝔟 A * 𝔟 (pw two (num 4 * q)) * e16
  have t1 := succ_le_two_pow (Γ := Γ) (num 16 * A)
  have u2 : Γ ⊢[PRAAx] le (num 16 * A * pw two (num 4 * q)) (pw two (num 16 * A) * pw two (num 4 * q)) := by
    ipra_le (sl t1 + 1) * 𝔟 (pw two (num 4 * q))
  have u4 : Γ ⊢[PRAAx] le (pw two (num 16 * A + num 4 * q)) (pw two ((num 4 + num 16 * A) * q)) :=
    pw_mono_exp h2 (by ipra_le 16 * 𝔟 A * sl hq)
  exact le_trans u1 (le_trans (le_congr (.eqRefl _) (pw_add _ _ _).eqSymm u2) u4)

end LeanProofs.IPRA.Foundations.DiagonalClock
