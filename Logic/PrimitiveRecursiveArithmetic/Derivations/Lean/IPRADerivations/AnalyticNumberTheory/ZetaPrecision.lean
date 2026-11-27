import IPRADerivations.AnalyticNumberTheory.ZetaErrorBudget

/-!
# The precision schedules of the zeta finite contract (`zeta_functional_equation_ipra`)

Packet: `analytic-number-theory/zeta_functional_equation_ipra`, `finite_contract.md`. The contract fixes every
working precision in advance ("there is no search for an adequate precision"); each choice is justified by an
explicit inequality between powers of two. Cleared of denominators (`a 2^{−s} ≤ 2^{−t}` as `a 2^t ≤ 2^s`):

* `err_tail_sharp`: "The first error is at most `2^(−p−7)`": `2 B! 2^{p+7} ≤ 2^{2T}`, `T = p + λ(B!) + 4`;
* `err_mesh_sharp`, `err_point_sharp`: "The last two are at most `2^(−p−4)` each": `T D 2^{p+4} ≤ 2^q` and
  `T 2^{p+4} ≤ 2^r`;
* `summand_exponent` (one summand of `JHat`, `v = u + 2U + C + 4`): "The exponent error is at most
  `C 2^{−v} ≤ 2^{−u−2U−4}`";
* `xi_budget` (the common xi approximation, `pJ = w + 4A + 8`): "the error is at most `4A² 2^{−pJ}`", which is at
  most `2^{−w}`;
* `factor_budget` (the remaining elementary factors, `v = w + 16A + 30`): the perturbation `4A 2^{−v}` times the
  exponential Lipschitz factor `2 exp(4A + 2) ≤ 2^{8A+5}` is at most `2^{−w−4}`.

The only estimate used is `ZetaErrorBudget.pow_absorb` (`x ≤ 2^L`, `L + c ≤ E` ⇒ `x 2^c ≤ 2^E`) with
`x ≤ 2^{λ(x)}`, `x ≤ 2^x` and `(A + 1)² ≤ 4^A` (`ZetaFiniteContract.sq_le_pow`). The analytic facts behind the
Lipschitz factors (`e ≤ 4`) are not derived here.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ZetaPrecision

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec le_pow_self sq_le_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaErrorBudget (pow_absorb Tp Dp qp rp)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- "The first error is at most `2^(−p−7)`": `2 B! 2^{p+7} ≤ 2^{2T}`. -/
theorem err_tail_sharp (p B : PTm n) :
    Γ ⊢[PRAAx] le (two * fact B * pw two (p + num 7)) (pw two (num 2 * Tp p B)) := by
  have hx := Prf.andE₁ (clog_spec (Γ := Γ) (fact B))
  have hE : Γ ⊢[PRAAx] le (clog (fact B) + succ (p + num 7)) (num 2 * Tp p B) := by
    ipra_le 𝔞 p + 𝔞 (clog (fact B))
  have a := pow_absorb hx hE
  have e := natEq (pw_succ (Γ := Γ) two (p + num 7))
  ipra_le sl a with 𝔞 (fact B) * e

/-- "The last two are at most `2^(−p−4)` each" — the mesh: `T D 2^{p+4} ≤ 2^q`. -/
theorem err_mesh_sharp (p B : PTm n) :
    Γ ⊢[PRAAx] le (Tp p B * Dp p B * pw two (p + num 4)) (pw two (qp p B)) :=
  pow_absorb (Prf.andE₁ (clog_spec (Γ := Γ) (Tp p B * Dp p B))) (by ipra_le 0)

/-- … and the point evaluation: `T 2^{p+4} ≤ 2^r`. -/
theorem err_point_sharp (p B : PTm n) : Γ ⊢[PRAAx] le (Tp p B * pw two (p + num 4)) (pw two (rp p B)) :=
  pow_absorb (Prf.andE₁ (clog_spec (Γ := Γ) (Tp p B))) (by ipra_le 0)

/-- One summand of `JHat`: with `v = u + 2U + C + 4`, `C 2^{−v} ≤ 2^{−u−2U−4}`. -/
theorem summand_exponent (u U C : PTm n) :
    Γ ⊢[PRAAx] le (C * pw two (u + num 2 * U + num 4)) (pw two (u + num 2 * U + C + num 4)) :=
  pow_absorb (le_pow_self C) (by ipra_le 0)

/-- `4A² ≤ 2^{2A+2}`. -/
theorem four_sq (A : PTm n) : Γ ⊢[PRAAx] le (num 4 * (A * A)) (pw two (succ (succ (A + A)))) := by
  have s := sq_le_pow (Γ := Γ) A
  have e1 := natEq (pw_succ (Γ := Γ) two (succ (A + A)))
  have e2 := natEq (pw_succ (Γ := Γ) two (A + A))
  have e3 := natEq (pw_add (Γ := Γ) two A A)
  ipra_le 4 * sl s + 8 * 𝔞 A + 4 with e1 + 2 * e2 + 4 * e3

/-- The common xi approximation: with `pJ = w + 4A + 8`, `4A² 2^{−pJ} ≤ 2^{−w}`. -/
theorem xi_budget (A w : PTm n) :
    Γ ⊢[PRAAx] le (num 4 * (A * A) * pw two w) (pw two (w + num 4 * A + num 8)) :=
  pow_absorb (four_sq A) (by ipra_le 2 * 𝔞 A + 6)

/-- The remaining elementary factors: with `v = w + 16A + 30`, the perturbation `4A 2^{−v}` times the Lipschitz
factor `2^{8A+5}` is at most `2^{−w−4}`. -/
theorem factor_budget (A w : PTm n) :
    Γ ⊢[PRAAx] le (num 4 * A * pw two (num 8 * A + num 5 + (w + num 4))) (pw two (w + num 16 * A + num 30)) := by
  have hA := le_pow_self (Γ := Γ) A
  have e1 := natEq (pw_succ (Γ := Γ) two (succ A))
  have e2 := natEq (pw_succ (Γ := Γ) two A)
  have hx : Γ ⊢[PRAAx] le (num 4 * A) (pw two (succ (succ A))) := by
    ipra_le 4 * sl hA with e1 + 2 * e2
  exact pow_absorb hx (by ipra_le 7 * 𝔞 A + 19)

end LeanProofs.IPRA.AnalyticNumberTheory.ZetaPrecision
