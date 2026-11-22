import IPRADerivations.Foundations.FormalDerivation

/-!
# Special cases of the hypergeometric equation by formal derivations

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/06_special.tex`:

* Theorem `thm:binomial` ("Generalized binomial identity"): `₂F₁(a, b; b; z) = (1 − z)^{−a}`, where
  "the right side means the normalized formal solution of `(1 − z) y′ − a y = 0`";
* Theorem `thm:log-special` ("Logarithm"): `₂F₁(1, 1; 2; −z) = log(1 + z)/z`, i.e.
  `₂F₁(1, 1; 2; w) = −log(1 − w)/w`;
* Theorem `thm:chebyshev` ("Generalized Chebyshev/cosine identity"): "Let `z = sin²(x/2)`. The chain
  rule transforms the hypergeometric equation with parameters `(a, −a, 1/2)` into `Y″ + a² Y = 0`."

With `ZExp.der δ` of `Foundations/FormalDerivation` and
`L_{a,b,c} y = z (1 − z) y″ + (c − (a + b + 1) z) y′ − ab y`:

* `binomial_ode`: a jet `y₀, y₁, y₂` with `(1 − z) y₁ = a y₀` and the derivative of this relation
  satisfies `L_{a,b,b} y = 0`, for every `b`;
* `log_ode`: with `u = 1/(1 − w)`, `t = 1/w` and `ℓ = −log(1 − w)` (`δ ℓ = u`), the function
  `g = ℓ t` satisfies `L_{1,1,2} g = 0`;
* `chebyshev_ode`: with `θ = x/2`, `sh = sin θ`, `ch = cos θ` (`δ sh = ch`, `δ ch = −sh`,
  `sh² + ch² = 1`), `z = sh²` and the chain rule `δ y₀ = y₁ δz`, `δ y₁ = y₂ δz`:
  `Y_θθ + 4a² Y = 4 · (z (1 − z) y₂ + (1/2 − z) y₁ + a² y₀)`, i.e. `Y_xx + a² Y` is the
  hypergeometric operator with parameters `(a, −a, 1/2)` applied to `y`.

The finite factorial identities of Theorem `thm:arcsin-special`,
`(1/2)_n / n! = C(2n, n)/4^n` and `(1/2)_n / (3/2)_n = 1/(2n + 1)`, are `df_cb` and `df_succ` of
`Probability/NormalMoments` (`(1/2)_n = (2n − 1)!!/2^n`).

The identification of the indeterminates with named analytic functions and the uniqueness of the
normalized solution are not formalized.
-/

namespace LeanProofs.IPRA.Analysis.HypergeometricSpecialCases

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The binomial case

Variables: `0 = z`, `1 = a`, `2 = b`, `3 = y₀`, `4 = y₁`, `5 = y₂`. -/

/-- `δ z = 1`, `δ y₀ = y₁`, `δ y₁ = y₂`. -/
def δB : Fin 6 → ZExp 6
  | ⟨0, _⟩ => 1
  | ⟨3, _⟩ => var 4
  | ⟨4, _⟩ => var 5
  | _ => 0

theorem δB_0 : δB 0 = 1 := rfl
theorem δB_1 : δB 1 = 0 := rfl
theorem δB_2 : δB 2 = 0 := rfl
theorem δB_3 : δB 3 = var 4 := rfl
theorem δB_4 : δB 4 = var 5 := rfl

/-- `thm:binomial`: a solution of `(1 − z) y′ = a y` solves the hypergeometric equation with parameters
`(a, b, b)`. The second hypothesis is the derivative of the first. -/
theorem binomial_ode :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [((1 - var 0) * var 4, var 1 * var 3),
          (der δB ((1 - var 0) * var 4), der δB (var 1 * var 3))]
        (var 0 * (1 - var 0) * var 5 + (var 2 - (var 1 + var 2 + 1) * var 0) * var 4 -
          var 1 * var 2 * var 3, 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δB_0, δB_1, δB_2, δB_3, δB_4]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 0 * h₂ + ρ 2 * h₁)

/-! ## The logarithm

Variables: `0 = w`, `1 = u = 1/(1 − w)`, `2 = t = 1/w`, `3 = ℓ = −log(1 − w)`. -/

/-- `δ w = 1`, `δ u = u²`, `δ t = −t²`, `δ ℓ = u`. -/
def δLg : Fin 4 → ZExp 4
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => var 1 * var 1
  | ⟨2, _⟩ => -(var 2 * var 2)
  | ⟨3, _⟩ => var 1

theorem δLg_0 : δLg 0 = 1 := rfl
theorem δLg_1 : δLg 1 = var 1 * var 1 := rfl
theorem δLg_2 : δLg 2 = -(var 2 * var 2) := rfl
theorem δLg_3 : δLg 3 = var 1 := rfl

/-- `thm:log-special`: `g = −log(1 − w)/w` satisfies `w (1 − w) g″ + (2 − 3w) g′ − g = 0`. -/
theorem log_ode :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [(var 1 * (1 - var 0), 1), (var 2 * var 0, 1)]
        (var 0 * (1 - var 0) * der δLg (der δLg (var 3 * var 2)) +
            (2 - 3 * var 0) * der δLg (var 3 * var 2) - var 3 * var 2, 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δLg_0, δLg_1, δLg_2, δLg_3]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (-2 * (ρ 2) ^ 2 * (ρ 0) + (ρ 2) * (ρ 1) * (ρ 0) + 2 * (ρ 2)) * h₁ +
      (-2 * (ρ 3) * (ρ 2) ^ 2 * (ρ 0) + 2 * (ρ 3) * (ρ 2) ^ 2 + (ρ 3) * (ρ 2) - 2 * (ρ 2)) * h₂)

/-! ## The Chebyshev case

Variables: `0 = sh = sin θ`, `1 = ch = cos θ`, `2 = a`, `3 = y₀`, `4 = y₁`, `5 = y₂`; `z = sh²`. -/

/-- `δ sh = ch`, `δ ch = −sh`, and the chain rule with `δ z = 2 sh ch`. -/
def δC : Fin 6 → ZExp 6
  | ⟨0, _⟩ => var 1
  | ⟨1, _⟩ => -(var 0)
  | ⟨3, _⟩ => var 4 * (2 * var 0 * var 1)
  | ⟨4, _⟩ => var 5 * (2 * var 0 * var 1)
  | _ => 0

theorem δC_0 : δC 0 = var 1 := rfl
theorem δC_1 : δC 1 = -(var 0) := rfl
theorem δC_2 : δC 2 = 0 := rfl
theorem δC_3 : δC 3 = var 4 * (2 * var 0 * var 1) := rfl
theorem δC_4 : δC 4 = var 5 * (2 * var 0 * var 1) := rfl

/-- `thm:chebyshev`: under `z = sin²(x/2)` the equation with parameters `(a, −a, 1/2)` becomes
`Y″ + a² Y = 0`; in the variable `θ = x/2`:
`Y_θθ + 4a² Y = 4 z (1 − z) y₂ + (2 − 4z) y₁ + 4a² y₀`. -/
theorem chebyshev_ode :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [(var 0 * var 0 + var 1 * var 1, 1)]
        (der δC (der δC (var 3)) + 4 * var 2 * var 2 * var 3,
          4 * (var 0 * var 0) * (1 - var 0 * var 0) * var 5 + (2 - 4 * (var 0 * var 0)) * var 4 +
            4 * var 2 * var 2 * var 3)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δC_0, δC_1, δC_2, δC_3, δC_4]
    linear_combination (4 * (ρ 0) ^ 2 * ρ 5 + 2 * ρ 4) * h)

end LeanProofs.IPRA.Analysis.HypergeometricSpecialCases
