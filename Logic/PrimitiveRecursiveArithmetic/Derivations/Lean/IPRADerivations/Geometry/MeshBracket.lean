import IPRADerivations.Core.Pairing
import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.AnalyticNumberTheory.Multiplicative

/-!
# The exact mesh bracket for rational square roots

Packet: `geometry/triangle_formulas_ipra`, Lemma `lem:mesh`: for a nonnegative rational `q = p/r`
(`r ≥ 1`) and `k ∈ ℕ`, the mesh root `ρ_k(q) = j/2^k` satisfies
`ρ_k(q)² ≤ q < (ρ_k(q) + 2^{-k})²`, i.e. with `S = 2^k`,

  `r j² ≤ p S² < r (j + 1)²`.

The packet obtains `j` as the last successful index of a bounded scan. Here `j` is the explicit
term `isqrt ⌊p S²/r⌋` (`Core/Pairing`), and the scan's answer is the same number: `mesh_unique`
shows that the bracket determines `j`.

* `mesh_lower`: `r j² ≤ p S²`, from `j² ≤ ⌊p S²/r⌋`;
* `mesh_upper`: `p S² < r (j + 1)²`, from `⌊p S²/r⌋ < (j + 1)²` and the remainder bound;
* `mesh_unique`: any `t` with `r t² ≤ p S² < r (t + 1)²` equals `j`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.MeshBracket

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `p S²` with `S = 2^k`. -/
abbrev XT (p k : PTm n) : PTm n := p * (pw two k * pw two k)

/-- The mesh numerator `j = isqrt ⌊p S²/r⌋`; the mesh root is `ρ_k(p/r) = j/2^k`. -/
abbrev rho (p r k : PTm n) : PTm n := isqrt (quo (XT p k) r)

variable {p r k : PTm n}

/-- Lower bracket: `r j² ≤ p S²`. -/
theorem mesh_lower (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) :
    Γ ⊢[PRAAx] le (r * (rho p r k * rho p r k)) (XT p k) := by
  have a := natEq (eq_add_of_le (isqrt_le (Γ := Γ) (quo (XT p k) r)))
  have d := natEq (div_eq (j := XT p k) hr)
  refine le_of_eq_add (d := r * monus (quo (XT p k) r) (rho p r k * rho p r k) + rem (XT p k) r) ?_
  apply deriveNat; ipra_simps
  linear_combination d + 𝔞 r * a

/-- Upper bracket: `p S² < r (j + 1)²`. -/
theorem mesh_upper (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) :
    Γ ⊢[PRAAx] lt (XT p k) (r * ((rho p r k + one) * (rho p r k + one))) := by
  have w₁ := natEq (eq_add_of_le (lt_isqrt_succ_sq (Γ := Γ) (quo (XT p k) r)))
  have w₂ := natEq (eq_add_of_le (rem_lt' hr (XT p k)))
  have d := natEq (div_eq (j := XT p k) hr)
  refine le_of_eq_add (d := r * monus ((rho p r k + one) * (rho p r k + one)) (succ (quo (XT p k) r)) +
    monus r (succ (rem (XT p k) r))) ?_
  apply deriveNat; ipra_simps
  linear_combination 𝔞 r * w₁ + w₂ - d

/-- The bracket determines the numerator: `r t² ≤ p S² < r (t + 1)²` gives `t = j`. -/
theorem mesh_unique (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) {t : PTm n}
    (h₁ : Γ ⊢[PRAAx] le (r * (t * t)) (XT p k))
    (h₂ : Γ ⊢[PRAAx] lt (XT p k) (r * ((t + one) * (t + one)))) :
    Γ ⊢[PRAAx] rho p r k ≐ t := by
  have dv := div_eq (j := XT p k) hr
  have rl := rem_lt' hr (XT p k)
  refine isqrt_unique ?_ ?_
  · refine .orE (lt_or_le (quo (XT p k) r) (t * t)) ?_ Prf.hyp0
    have w := natEq (eq_add_of_le (Prf.hyp0 : (lt (quo (XT p k) r) (t * t) :: Γ) ⊢[PRAAx] _))
    have e₁ := natEq (eq_add_of_le (h₁.wk (ψ := lt (quo (XT p k) r) (t * t))))
    have e₂ := natEq (dv.wk (ψ := lt (quo (XT p k) r) (t * t)))
    have e₃ := natEq (eq_add_of_le (rl.wk (ψ := lt (quo (XT p k) r) (t * t))))
    refine succ_ne_zero' _ (a := monus r (succ (rem (XT p k) r)) +
      r * monus (t * t) (succ (quo (XT p k) r)) + monus (XT p k) (r * (t * t))) ?_
    apply deriveNat; ipra_simps
    linear_combination -e₁ + e₂ - 𝔞 r * w - e₃
  · refine .orE (lt_or_le (quo (XT p k) r) ((t + one) * (t + one))) Prf.hyp0 ?_
    have w := natEq (eq_add_of_le (Prf.hyp0 : (le ((t + one) * (t + one)) (quo (XT p k) r) :: Γ) ⊢[PRAAx] _))
    have e₁ := natEq (eq_add_of_le (h₂.wk (ψ := le ((t + one) * (t + one)) (quo (XT p k) r))))
    have e₂ := natEq (dv.wk (ψ := le ((t + one) * (t + one)) (quo (XT p k) r)))
    refine succ_ne_zero' _ (a := r * monus (quo (XT p k) r) ((t + one) * (t + one)) + rem (XT p k) r +
      monus (r * ((t + one) * (t + one))) (succ (XT p k))) ?_
    apply deriveNat; ipra_simps
    linear_combination -e₁ - e₂ - 𝔞 r * w

end LeanProofs.IPRA.Geometry.MeshBracket
