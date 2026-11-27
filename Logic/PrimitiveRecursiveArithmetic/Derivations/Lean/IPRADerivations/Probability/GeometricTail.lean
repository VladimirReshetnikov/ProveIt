import IPRADerivations.Probability.GeometricMean
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# The tail modulus of the geometric mean

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:geometric`, the tail: "Since `q < 1`, a
rational separation `q ≤ 1 − 1/d` is computable from the rational code for `p > 0`. The finite binomial
inequality `(1 − 1/d)^d ≤ 1/2` gives `q^{dm} ≤ 2^{−m}`."

* `bern_hom`: the homogeneous Bernoulli inequality `a^{m+1} + (m+1) a^m b ≤ (a + b)^{m+1}`, by quantifier-free
  induction on `m`;
* `half_bound`: `(1 − 1/d)^d ≤ 1/2`, cleared: `2 e^{e+1} ≤ (e + 1)^{e+1}` for `d = e + 1`;
* `power_half`: `q^{dm} ≤ 2^{−m}` for `q = e/(e + 1)`, cleared: `2^m (e^d)^m ≤ (d^d)^m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.GeometricTail

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias bern_base := LeanProofs.IPRA.pw_bernoulli_base
alias bern_step := LeanProofs.IPRA.pw_bernoulli_step

/-- The homogeneous Bernoulli inequality `a^{m+1} + (m+1) a^m b ≤ (a + b)^{m+1}`. -/
alias bern_hom := LeanProofs.IPRA.pw_bernoulli

/-- `(1 − 1/d)^d ≤ 1/2`, cleared: `2 e^{e+1} ≤ (e + 1)^{e+1}`. -/
theorem half_bound (e : PTm n) : Γ ⊢[PRAAx] le (num 2 * pw e (succ e)) (pw (succ e) (succ e)) :=
  pw_bernoulli_half e

/-- `q^{dm} ≤ 2^{−m}` for `q = e/(e + 1)`, `d = e + 1`: `2^m (e^d)^m ≤ (d^d)^m`. -/
theorem power_half (e m : PTm n) :
    Γ ⊢[PRAAx] le (pw (num 2) m * pw (pw e (succ e)) m) (pw (pw (succ e) (succ e)) m) := by
  refine le_congr (mul_pw _ _ m) (.eqRefl _) (pw_le_pw m (half_bound e))

end LeanProofs.IPRA.Probability.GeometricTail
