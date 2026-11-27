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

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `p S²` with `S = 2^k`. -/
abbrev XT (p k : PTm n) : PTm n := p * (pw two k * pw two k)

/-- The mesh numerator `j = isqrt ⌊p S²/r⌋`; the mesh root is `ρ_k(p/r) = j/2^k`. -/
abbrev rho (p r k : PTm n) : PTm n := isqrt (quo (XT p k) r)

variable {p r k : PTm n}

/-- Lower bracket: `r j² ≤ p S²`. -/
theorem mesh_lower (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) :
    Γ ⊢[PRAAx] le (r * (rho p r k * rho p r k)) (XT p k) :=
  le_trans (mul_le_mul_left r (isqrt_le _)) (Division.mul_quo_le hr)

/-- Upper bracket: `p S² < r (j + 1)²`. -/
theorem mesh_upper (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) :
    Γ ⊢[PRAAx] lt (XT p k) (r * ((rho p r k + one) * (rho p r k + one))) := by
  exact lt_of_lt_of_le (Division.lt_mul_succ_quo hr)
    (mul_le_mul_left r (lt_isqrt_succ_sq _))

/-- The bracket determines the numerator: `r t² ≤ p S² < r (t + 1)²` gives `t = j`. -/
theorem mesh_unique (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) {t : PTm n}
    (h₁ : Γ ⊢[PRAAx] le (r * (t * t)) (XT p k))
    (h₂ : Γ ⊢[PRAAx] lt (XT p k) (r * ((t + one) * (t + one)))) :
    Γ ⊢[PRAAx] rho p r k ≐ t :=
  isqrt_unique (Division.le_quo_of_mul_le hr h₁) (Division.quo_lt_of_lt_mul hr h₂)

end LeanProofs.IPRA.Geometry.MeshBracket
