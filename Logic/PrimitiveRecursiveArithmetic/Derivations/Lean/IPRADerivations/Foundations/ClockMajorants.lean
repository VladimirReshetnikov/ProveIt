import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Analysis.RationalClosure

/-!
# Majorants of composed polynomial clocks

Packet: `foundations/ipra_complexity_foundations_2026-11-20`, `tex/machines.tex`, "Clock families and asymptotic
bounds": for the monomial clocks `p_{c,k}(n) = c(n + 1)^k`, "Sums and compositions have explicit majorants: for
`p = a(n+1)^r`, `q = b(n+1)^s`, with `r, s ≥ 1`,
`p(n) + q(p(n)) + n + 1 ≤ (a + b(a+1)^s + 1)(n+1)^{max(r, rs, 1)}`. This follows by `p(n) + 1 ≤ (a+1)(n+1)^r`,
multiplication, and monotonicity of powers." (With `r, s ≥ 1` the maximum is `rs`.) It is the arithmetic behind
the composition of polynomial reductions (`thm:reduction`).

* `pw_mono_exp`: `x ≥ 1` and `k ≤ l` give `x^k ≤ x^l`;
* `compose_majorant`: the displayed bound, for all object terms `a, b, r, s, n` with `r, s ≥ 1`;
* `exp_majorant` (`thm:closure`, `NP ⊆ EXP`): the exhaustive certificate scan costs `A 2^{p(n)} M^b` with
  `M = n + p(n) + q(n) + 1`; "replace the polynomial factor and `A` by powers of two using `r ≤ 2^r`":
  `A 2^p M^b ≤ 2^{A + p + M b}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ClockMajorants

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (one_le_pw_of)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Monotonicity of powers in the exponent: `x ≥ 1`, `k ≤ l` give `x^k ≤ x^l`. -/
theorem pw_mono_exp {x k l : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hkl : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] le (pw x k) (pw x l) := by
  have e : Γ ⊢[PRAAx] pw x l ≐ pw x k * pw x (monus l k) :=
    (congrAp2 powF (eq_add_of_le hkl) (.eqRefl x)).eqTrans (pw_add _ _ _)
  have hp := one_le_pw_of (Γ := Γ) (monus l k) hx
  have e' := natEq e
  ipra_le 𝔟 (pw x k) * sl hp with e'

/-- `p(n) + q(p(n)) + n + 1 ≤ (a + b(a+1)^s + 1)(n+1)^{rs}` for `p = a(n+1)^r`, `q(m) = b(m+1)^s`. -/
theorem compose_majorant {a b r s : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (k : PTm n) :
    Γ ⊢[PRAAx] le (a * pw (succ k) r + b * pw (succ (a * pw (succ k) r)) s + succ k)
      ((a + b * pw (succ a) s + one) * pw (succ k) (r * s)) := by
  have hN : Γ ⊢[PRAAx] le one (succ k) := by ipra_le 𝔟 k
  have hrs : Γ ⊢[PRAAx] le r (r * s) := by ipra_le 𝔟 r * sl hs
  have h1rs : Γ ⊢[PRAAx] le one (r * s) := by ipra_le sl hr * 𝔟 s + sl hs
  have m1 := pw_mono_exp hN hrs
  have m2 : Γ ⊢[PRAAx] le (succ k) (pw (succ k) (r * s)) :=
    le_congr (pw_one _) (.eqRefl _) (pw_mono_exp hN h1rs)
  have hP := one_le_pw_of (Γ := Γ) r hN
  have h1 : Γ ⊢[PRAAx] le (succ (a * pw (succ k) r)) (succ a * pw (succ k) r) := by ipra_le sl hP
  have h2 : Γ ⊢[PRAAx] le (pw (succ (a * pw (succ k) r)) s) (pw (succ a) s * pw (succ k) (r * s)) :=
    le_congr (.eqRefl _) ((mul_pw _ _ _).eqTrans (congrMul (.eqRefl _) (pw_mul _ _ _))) (pw_le_pw s h1)
  ipra_le 𝔟 a * sl m1 + 𝔟 b * sl h2 + sl m2

/-- `A 2^p M^b ≤ 2^{A + p + Mb}`, from `A < 2^A` and `M < 2^M`. -/
theorem exp_majorant (A p M b : PTm n) :
    Γ ⊢[PRAAx] le (A * pw two p * pw M b) (pw two (A + p + M * b)) := by
  have hA0 := succ_le_two_pow (Γ := Γ) A
  have hA : Γ ⊢[PRAAx] le A (pw two A) := by ipra_le sl hA0 + 1
  have hM0 := succ_le_two_pow (Γ := Γ) M
  have hM : Γ ⊢[PRAAx] le M (pw two M) := by ipra_le sl hM0 + 1
  have h3 := pw_le_pw b hM
  have e1 := natEq (pw_add (Γ := Γ) two (A + p) (M * b))
  have e2 := natEq (pw_add (Γ := Γ) two A p)
  have e3 := natEq (pw_mul (Γ := Γ) two M b)
  ipra_le 𝔟 (pw two p) * (sl hA * 𝔟 (pw (pw two M) b) + 𝔟 A * sl h3) with
    e1 + 𝔟 (pw two (M * b)) * e2 - 𝔟 (pw two A) * 𝔟 (pw two p) * e3

end LeanProofs.IPRA.Foundations.ClockMajorants
