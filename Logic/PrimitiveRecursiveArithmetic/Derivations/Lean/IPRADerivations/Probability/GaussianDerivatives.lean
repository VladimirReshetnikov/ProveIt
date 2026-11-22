import IPRADerivations.Foundations.FormalDerivation

/-!
# Differential identities of the normal density by formal derivations

Packet: `probability/normal_distribution_ipra_2026-11-16`:

* Proposition `prop:gaussian-odes`: `φ′ + x φ = 0`, `Φ″ + x Φ′ = 0`, and the uniqueness argument
  "`d/dx (e^{x²/2} (u − v)) = 0`";
* Proposition `prop:shape`: `φ″ = (x² − 1) φ`; for `N(μ, σ²)` the inflection points are `μ ± σ`;
* Theorem `thm:hermite-derivatives`, the step of its proof: "`φ^{(n+1)} = (−1)^n (He_n′ − x He_n) φ`";
* Theorem `thm:mills`: "A finite differentiation gives `h′(x) = −2φ(x)/(1 + x²)²`" for
  `h = Q − x φ/(1 + x²)`, `Q = 1 − Φ`;
* Theorem `thm:mills-expansion`, the step of the tail expansion:
  `(φ/x^{2k+1})′ = −φ/x^{2k} − (2k + 1) φ/x^{2k+2}`;
* Theorem `thm:stein`, the local identity of its proof: `f′ = −(x − μ) f/σ²`, hence
  `σ² (g f)′ = σ² g′ f − (x − μ) g f`.

The functions are indeterminates with derivative rules (`Foundations/FormalDerivation`): `δ φ = −x φ`,
`δ Φ = φ`, `δ H = H′`, `δ E = x E` for `E = e^{x²/2}`, `δ r = −r²` for `r = 1/x`,
`δ R = −(2k + 1) R r` for `R = r^{2k+1}`; for the general density `δ f = −(x − μ) ς f` with `ς = 1/σ²`
(hypothesis `ς σ² = 1`).

* `phi_second`, `cdf_ode`, `hermite_step`, `integrating_factor`, `mills_derivative`, `tail_step`;
* `density_ode`, `inflection`, `stein_local` for `N(μ, σ²)`.

Closed sentences of iPRA about signed integer variables. The identification with the named functions,
the integrals and the limits at infinity are not formalized.
-/

namespace LeanProofs.IPRA.Probability.GaussianDerivatives

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The standard normal

Variables: `0 = x`, `1 = φ`, `2 = Φ`, `3 = H`, `4 = H′`, `5 = E`, `6 = v`, `7 = r`, `8 = k`, `9 = R`. -/

/-- The derivation of the standard normal calculus. -/
def δG : Fin 10 → ZExp 10
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -(var 0 * var 1)
  | ⟨2, _⟩ => var 1
  | ⟨3, _⟩ => var 4
  | ⟨5, _⟩ => var 0 * var 5
  | ⟨6, _⟩ => -(var 0 * var 6)
  | ⟨7, _⟩ => -(var 7 * var 7)
  | ⟨9, _⟩ => -((2 * var 8 + 1) * var 9 * var 7)
  | _ => 0

theorem δG_0 : δG 0 = 1 := rfl
theorem δG_1 : δG 1 = -(var 0 * var 1) := rfl
theorem δG_2 : δG 2 = var 1 := rfl
theorem δG_3 : δG 3 = var 4 := rfl
theorem δG_4 : δG 4 = 0 := rfl
theorem δG_5 : δG 5 = var 0 * var 5 := rfl
theorem δG_6 : δG 6 = -(var 0 * var 6) := rfl
theorem δG_7 : δG 7 = -(var 7 * var 7) := rfl
theorem δG_8 : δG 8 = 0 := rfl
theorem δG_9 : δG 9 = -((2 * var 8 + 1) * var 9 * var 7) := rfl

/-- `prop:shape`: `φ″ = (x² − 1) φ`. -/
theorem phi_second :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (der δG (der δG (var 1)), (var 0 * var 0 - 1) * var 1)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δG_0, δG_1, δG_2, δG_3, δG_4, δG_5, δG_6, δG_7, δG_8, δG_9]; ring)

/-- `prop:gaussian-odes`: `Φ″ + x Φ′ = 0`. -/
theorem cdf_ode :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (der δG (der δG (var 2)) + var 0 * der δG (var 2), 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δG_0, δG_1, δG_2, δG_3, δG_4, δG_5, δG_6, δG_7, δG_8, δG_9]; ring)

/-- `thm:hermite-derivatives`, the step: `(H φ)′ = (H′ − x H) φ`. -/
theorem hermite_step :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (der δG (var 3 * var 1), (var 4 - var 0 * var 3) * var 1)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δG_0, δG_1, δG_2, δG_3, δG_4, δG_5, δG_6, δG_7, δG_8, δG_9]; ring)

/-- `prop:gaussian-odes`, uniqueness: `(e^{x²/2} (u − v))′ = 0` for two solutions of `y′ + x y = 0`. -/
theorem integrating_factor :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (der δG (var 5 * (var 1 - var 6)), 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δG_0, δG_1, δG_2, δG_3, δG_4, δG_5, δG_6, δG_7, δG_8, δG_9]; ring)

/-- `h = (1 − Φ) − x φ/(1 + x²)`. -/
abbrev hM : Frac 10 := Frac.ofZ (1 - var 2) - ⟨var 0 * var 1, 1 + var 0 * var 0⟩

/-- `thm:mills`: `h′ = −2φ/(1 + x²)²`. -/
theorem mills_derivative :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (Frac.eqn (Frac.d δG hM)
        ⟨-(2 * var 1), (1 + var 0 * var 0) * (1 + var 0 * var 0)⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δG_0, δG_1, δG_2, δG_3, δG_4, δG_5, δG_6, δG_7, δG_8, δG_9]; ring)

/-- `thm:mills-expansion`, the step: `(φ R)′ = −φ (R x) − (2k + 1) φ (R r)` for `R = r^{2k+1}`,
`r = 1/x`, i.e. `(φ/x^{2k+1})′ = −φ/x^{2k} − (2k + 1) φ/x^{2k+2}`. -/
theorem tail_step :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (der δG (var 1 * var 9),
        -(var 1 * (var 9 * var 0)) - (2 * var 8 + 1) * (var 1 * (var 9 * var 7)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δG_0, δG_1, δG_2, δG_3, δG_4, δG_5, δG_6, δG_7, δG_8, δG_9]; ring)

/-! ## The general normal density

Variables: `0 = x`, `1 = μ`, `2 = σ²`, `3 = ς = 1/σ²`, `4 = f`, `5 = g`, `6 = g′`. -/

/-- `δ f = −(x − μ) ς f`, `δ g = g′`. -/
def δN : Fin 7 → ZExp 7
  | ⟨0, _⟩ => 1
  | ⟨4, _⟩ => -((var 0 - var 1) * var 3 * var 4)
  | ⟨5, _⟩ => var 6
  | _ => 0

theorem δN_0 : δN 0 = 1 := rfl
theorem δN_1 : δN 1 = 0 := rfl
theorem δN_2 : δN 2 = 0 := rfl
theorem δN_3 : δN 3 = 0 := rfl
theorem δN_4 : δN 4 = -((var 0 - var 1) * var 3 * var 4) := rfl
theorem δN_5 : δN 5 = var 6 := rfl
theorem δN_6 : δN 6 = 0 := rfl

/-- `σ² f′ + (x − μ) f = 0`. -/
theorem density_ode :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(var 3 * var 2, 1)] (var 2 * der δN (var 4) + (var 0 - var 1) * var 4, 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δN_0, δN_1, δN_2, δN_3, δN_4, δN_5, δN_6]
    linear_combination (-((ρ 0 - ρ 1) * ρ 4)) * h)

/-- `prop:shape` for `N(μ, σ²)`: `σ⁴ f″ = ((x − μ)² − σ²) f`, so the inflection points are `μ ± σ`. -/
theorem inflection :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(var 3 * var 2, 1)]
        (var 2 * var 2 * der δN (der δN (var 4)),
          ((var 0 - var 1) * (var 0 - var 1) - var 2) * var 4)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δN_0, δN_1, δN_2, δN_3, δN_4, δN_5, δN_6]
    linear_combination (ρ 4 * (-(ρ 2) + (ρ 0 - ρ 1) ^ 2 * (ρ 3 * ρ 2 + 1))) * h)

/-- `thm:stein`, the local identity: `σ² (g f)′ = σ² g′ f − (x − μ) g f`. -/
theorem stein_local :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(var 3 * var 2, 1)]
        (var 2 * der δN (var 5 * var 4),
          var 2 * var 6 * var 4 - (var 0 - var 1) * var 5 * var 4)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δN_0, δN_1, δN_2, δN_3, δN_4, δN_5, δN_6]
    linear_combination (-((ρ 0 - ρ 1) * ρ 5 * ρ 4)) * h)

end LeanProofs.IPRA.Probability.GaussianDerivatives
