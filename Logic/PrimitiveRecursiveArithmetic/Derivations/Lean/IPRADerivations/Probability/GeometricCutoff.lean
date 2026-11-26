import IPRADerivations.Probability.GeometricTail
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid

/-!
# An explicit cutoff for the geometric mean

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:geometric`, the end of the tail modulus:
"Bounded search therefore chooses `m` with `(dm + d) 2^{−m} ≤ 2^{−r}`, yielding a primitive-recursive stage
`N = dm` at which `(N + 1) q^N ≤ 2^{−r}`." Instead of a search, `m = 2K` with `K = r + 2 + d` works.

For `q = u/v ≤ e/(e + 1)` (`d = e + 1`), with `N = d m`:

* `pow_bound`: `2^m u^N ≤ v^N` (`q^N ≤ 2^{−m}`, from `GeometricTail.power_half` and `q ≤ e/d`, then cancelling
  `d^N ≥ 1`);
* `cutoff_bound`: `(N + 1) 2^r ≤ 2^m` (`2^K ≥ 2^r · 4 · 2^d`, `2^K ≥ K + 1`, `2^d ≥ d + 1`);
* `geometric_cutoff`: `(N + 1) 2^r u^N ≤ v^N`, i.e. `(N + 1) q^N ≤ 2^{−r}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.GeometricCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (cancel_pos one_le_pw_of)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Probability.GeometricTail (power_half)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `K = r + 2 + d`, `d = e + 1`. -/
abbrev KT (e r : PTm n) : PTm n := r + (two + succ e)
/-- `m = 2K`. -/
abbrev mT (e r : PTm n) : PTm n := KT e r + KT e r
/-- `N = d m`. -/
abbrev NT (e r : PTm n) : PTm n := succ e * mT e r

/-- `q ≤ e/d` gives `q^N ≤ 2^{−m}`: `2^m u^N ≤ v^N`. -/
theorem pow_bound {e r u v : PTm n} (hq : Γ ⊢[PRAAx] le (u * succ e) (e * v)) :
    Γ ⊢[PRAAx] le (pw two (mT e r) * pw u (NT e r)) (pw v (NT e r)) := by
  have A := le_congr (mul_pw _ _ _) (mul_pw _ _ _) (pw_le_pw (NT e r) hq)
  have B : Γ ⊢[PRAAx] le (pw two (mT e r) * pw e (NT e r)) (pw (succ e) (NT e r)) :=
    le_congr (congrMul (.eqRefl _) (pw_mul e (succ e) (mT e r)))
    (pw_mul (succ e) (succ e) (mT e r)) (power_half (Γ := Γ) e (mT e r))
  have hD := one_le_pw_of (Γ := Γ) (NT e r) (show Γ ⊢[PRAAx] le one (succ e) by ipra_le 𝔟 e)
  refine cancel_pos hD ?_
  ipra_le 𝔟 (pw v (NT e r)) * sl B + 𝔟 (pw two (mT e r)) * sl A

/-- `(N + 1) 2^r ≤ 2^m`. -/
theorem cutoff_bound (e r : PTm n) : Γ ⊢[PRAAx] le (succ (NT e r) * pw two r) (pw two (mT e r)) := by
  have sB := succ_le_two_pow (Γ := Γ) (KT e r)
  have sD := succ_le_two_pow (Γ := Γ) (succ e)
  have e1 := natEq (pw_add (Γ := Γ) two (KT e r) (KT e r))
  have e2 := natEq (pw_add (Γ := Γ) two r (two + succ e))
  have e3 := natEq (pw_add (Γ := Γ) two two (succ e))
  have e4 := natEq ((pw_succ (Γ := Γ) two one).eqTrans (congrMul (pw_one two) (.eqRefl two)))
  ipra_le 𝔟 (pw two r) * (4 * sl sD * sl sB + 4 * sl sD * (𝔟 (KT e r) + 1) + 4 * (𝔟 e + 2) * sl sB +
      2 * (𝔟 e + 1) * 𝔟 (KT e r) + 4 * (𝔟 e + 1) + 4 * 𝔟 (KT e r) + 3) using
    rw [e1, e2, e3, e4]; ring

/-- `prop:geometric`, the tail at the explicit stage `N = d m`: `(N + 1) q^N ≤ 2^{−r}`. -/
theorem geometric_cutoff {e r u v : PTm n} (hq : Γ ⊢[PRAAx] le (u * succ e) (e * v)) :
    Γ ⊢[PRAAx] le (succ (NT e r) * pw two r * pw u (NT e r)) (pw v (NT e r)) := by
  have C := pow_bound (r := r) hq
  have D := cutoff_bound (Γ := Γ) e r
  ipra_le sl C + 𝔟 (pw u (NT e r)) * sl D

end LeanProofs.IPRA.Probability.GeometricCutoff
