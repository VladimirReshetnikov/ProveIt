import IPRADerivations.Foundations.FormalDerivation

/-!
# The hypergeometric equation under formal derivations: Euler, Pfaff, Wronskian, Q-form, Jacobi

Packet: `analysis/hypergeometric_ipra_2026-11-16`: Lemma `lem:pullback-certificate` with Theorem
`thm:euler-transform` and Theorem `thm:pfaff` (`sections/07_transformations.tex`), Lemma `lem:wronskian`
and Proposition `prop:q-form` (`sections/05_ode.tex`), and the substitution in Theorem `thm:jacobi` (`sections/06_special.tex`).

Here the differentiations themselves are formal objects: `ZExp.der δ` of
`Foundations/FormalDerivation` differentiates polynomial expressions, with prescribed values on the
variables. Functions that are not polynomials enter as indeterminates with their derivative rules:

* `u` stands for `1/(1 − z)`, with the hypothesis `u (1 − z) = 1` and `δ u = u²`;
* `p` stands for the prefactor, with `δ p = −(c − a − b) p u` for `p = (1 − z)^{c−a−b}` (Euler) and
  `δ p = a p u` for `p = (1 − z)^{−a}` (Pfaff);
* `v₀, v₁, v₂` stand for a solution `v` of the source equation and its derivatives at the inner
  point: `δ v₀ = v₁ φ′`, `δ v₁ = v₂ φ′` (chain rule), with `φ′ = 1` for Euler and
  `φ′ = −u − z u²` for `φ = z/(z − 1) = −z u` (Pfaff).

With `Lh δ z A B C g = z (1 − z) g″ + (C − (A + B + 1) z) g′ − AB g`:

* `euler_transform`: if `v` solves the equation with parameters `(c − a, c − b, c)`, then
  `g = p v` solves the one with parameters `(a, b, c)`;
* `pfaff_transform`: if `v` solves the equation with parameters `(a, c − b, c)` at `w = −z u`, then
  `g = p · v(φ)` solves the one with parameters `(a, b, c)`;
* `wronskian_formal`: for two solutions of `y″ + P y′ + Q y = 0`, the derivative of
  `W = y₁ y₂′ − y₁′ y₂` is `−P W`;
* `q_form_formal` (`prop:q-form`): for `y = m U` with the gauge factor `m′ = −(P/2) m`,
  `4z(1 − z) · L y = m · (4z²(1 − z)² U″ + N(z) U)` with the printed numerator `N` of `Q`;
* `jacobi_equation`: with `2z = 1 − t` and `d/dz = −2 d/dt` (so `δ t = −2`, `δ Y₀ = −2 Y₁`,
  `δ Y₁ = −2 Y₂` for the `t`-derivatives `Y₁, Y₂` of `Y₀`), the hypergeometric operator with
  `a = −n`, `b = n + α + β + 1`, `c = α + 1` applied to `Y₀` equals the Jacobi operator
  `(1 − t²) Y₂ + (β − α − (α + β + 2) t) Y₁ + n (n + α + β + 1) Y₀`.

Each statement is a closed sentence of iPRA: an implication between polynomial equations in signed
integer variables, certified in every commutative ring by an explicit combination of the hypotheses
(the cofactors were computed by polynomial division and are checked by `linear_combination`). The
identification of the indeterminates with named analytic functions, and the uniqueness of the
normalized solution, are not formalized.
-/

namespace LeanProofs.IPRA.Analysis.HypergeometricOdeFormal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-- The hypergeometric operator `z (1 − z) g″ + (C − (A + B + 1) z) g′ − AB g` for the derivation `δ`. -/
def Lh {k : ℕ} (δ : Fin k → ZExp k) (zz A B C g : ZExp k) : ZExp k :=
  zz * (1 - zz) * der δ (der δ g) + (C - (A + B + 1) * zz) * der δ g - A * B * g

/-! ## Euler and Pfaff

Variables: `0 = z`, `1 = a`, `2 = b`, `3 = c`, `4 = u`, `5 = p`, `6 = v₀`, `7 = v₁`, `8 = v₂`. -/

/-- The derivation for the Euler transformation. -/
def δE : Fin 9 → ZExp 9
  | ⟨0, _⟩ => 1
  | ⟨4, _⟩ => var 4 * var 4
  | ⟨5, _⟩ => -((var 3 - var 1 - var 2) * var 5 * var 4)
  | ⟨6, _⟩ => var 7
  | ⟨7, _⟩ => var 8
  | _ => 0

theorem δE_0 : δE 0 = 1 := rfl
theorem δE_1 : δE 1 = 0 := rfl
theorem δE_2 : δE 2 = 0 := rfl
theorem δE_3 : δE 3 = 0 := rfl
theorem δE_4 : δE 4 = var 4 * var 4 := rfl
theorem δE_5 : δE 5 = -((var 3 - var 1 - var 2) * var 5 * var 4) := rfl
theorem δE_6 : δE 6 = var 7 := rfl
theorem δE_7 : δE 7 = var 8 := rfl
theorem δE_8 : δE 8 = 0 := rfl

/-- `thm:euler-transform` as a formal differential identity. -/
theorem euler_transform :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [(var 4 * (1 - var 0), 1),
          (var 0 * (1 - var 0) * var 8 +
              (var 3 - ((var 3 - var 1) + (var 3 - var 2) + 1) * var 0) * var 7 -
            (var 3 - var 1) * (var 3 - var 2) * var 6, 0)]
        (Lh δE (var 0) (var 1) (var 2) (var 3) (var 5 * var 6), 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Lh, δE_0, δE_1, δE_2, δE_3, δE_4, δE_5, δE_6, δE_7, δE_8]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ((ρ 5)) * h₂ +
      ((ρ 1)^2*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + 2*(ρ 1)*(ρ 2)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) - 2*(ρ 1)*(ρ 3)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + (ρ 1)*(ρ 3)*(ρ 5)*(ρ 6) + (ρ 1)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + 2*(ρ 1)*(ρ 5)*(ρ 7)*(ρ 0) + (ρ 2)^2*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) - 2*(ρ 2)*(ρ 3)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + (ρ 2)*(ρ 3)*(ρ 5)*(ρ 6) + (ρ 2)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + 2*(ρ 2)*(ρ 5)*(ρ 7)*(ρ 0) + (ρ 3)^2*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) - (ρ 3)^2*(ρ 5)*(ρ 6) - (ρ 3)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) - 2*(ρ 3)*(ρ 5)*(ρ 7)*(ρ 0)) * h₁)

/-- The derivation for the Pfaff transformation; `φ′ = −u − z u²`. -/
def δP : Fin 9 → ZExp 9
  | ⟨0, _⟩ => 1
  | ⟨4, _⟩ => var 4 * var 4
  | ⟨5, _⟩ => var 1 * var 5 * var 4
  | ⟨6, _⟩ => var 7 * (-(var 4) - var 0 * (var 4 * var 4))
  | ⟨7, _⟩ => var 8 * (-(var 4) - var 0 * (var 4 * var 4))
  | _ => 0

theorem δP_0 : δP 0 = 1 := rfl
theorem δP_1 : δP 1 = 0 := rfl
theorem δP_2 : δP 2 = 0 := rfl
theorem δP_3 : δP 3 = 0 := rfl
theorem δP_4 : δP 4 = var 4 * var 4 := rfl
theorem δP_5 : δP 5 = var 1 * var 5 * var 4 := rfl
theorem δP_6 : δP 6 = var 7 * (-(var 4) - var 0 * (var 4 * var 4)) := rfl
theorem δP_7 : δP 7 = var 8 * (-(var 4) - var 0 * (var 4 * var 4)) := rfl
theorem δP_8 : δP 8 = 0 := rfl

/-- `thm:pfaff` (first formula) as a formal differential identity; the source equation is taken at
`w = −z u`. -/
theorem pfaff_transform :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [(var 4 * (1 - var 0), 1),
          (-(var 0 * var 4) * (1 - -(var 0 * var 4)) * var 8 +
              (var 3 - (var 1 + (var 3 - var 2) + 1) * -(var 0 * var 4)) * var 7 -
            var 1 * (var 3 - var 2) * var 6, 0)]
        (Lh δP (var 0) (var 1) (var 2) (var 3) (var 5 * var 6), 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Lh, δP_0, δP_1, δP_2, δP_3, δP_4, δP_5, δP_6, δP_7, δP_8]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ((ρ 5)*(ρ 4)^2*(ρ 0)^2 - (ρ 5)*(ρ 4)^2*(ρ 0) + (ρ 5)*(ρ 4)*(ρ 0) - (ρ 5)*(ρ 4)) * h₂ +
      ((ρ 1)^2*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + (ρ 1)*(ρ 2)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) + (ρ 1)*(ρ 2)*(ρ 5)*(ρ 6) - (ρ 1)*(ρ 3)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) - (ρ 1)*(ρ 5)*(ρ 4)^2*(ρ 7)*(ρ 0)^2 + (ρ 1)*(ρ 5)*(ρ 4)*(ρ 6)*(ρ 0) - (ρ 1)*(ρ 5)*(ρ 4)*(ρ 7)*(ρ 0) - (ρ 2)*(ρ 5)*(ρ 4)^2*(ρ 7)*(ρ 0)^2 - (ρ 2)*(ρ 5)*(ρ 4)*(ρ 7)*(ρ 0) + (ρ 3)*(ρ 5)*(ρ 4)^2*(ρ 7)*(ρ 0)^2 + (ρ 3)*(ρ 5)*(ρ 4)*(ρ 7)*(ρ 0) - (ρ 5)*(ρ 4)^2*(ρ 7)*(ρ 0)^2 - (ρ 5)*(ρ 4)*(ρ 7)*(ρ 0)) * h₁)

/-! ## The Wronskian

Variables: `0 = y₁`, `1 = y₁′`, `2 = y₁″`, `3 = y₂`, `4 = y₂′`, `5 = y₂″`, `6 = P`, `7 = Q`. -/

/-- The derivation `y ↦ y′ ↦ y″` for two functions. -/
def δW : Fin 8 → ZExp 8
  | ⟨0, _⟩ => var 1
  | ⟨1, _⟩ => var 2
  | ⟨3, _⟩ => var 4
  | ⟨4, _⟩ => var 5
  | _ => 0

theorem δW_0 : δW 0 = var 1 := rfl
theorem δW_1 : δW 1 = var 2 := rfl
theorem δW_3 : δW 3 = var 4 := rfl
theorem δW_4 : δW 4 = var 5 := rfl

/-- `lem:wronskian`: `W′ = −P W` for `W = y₁ y₂′ − y₁′ y₂`. -/
theorem wronskian_formal :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(var 2 + var 6 * var 1 + var 7 * var 0, 0), (var 5 + var 6 * var 4 + var 7 * var 3, 0)]
        (der δW (var 0 * var 4 - var 1 * var 3), -(var 6 * (var 0 * var 4 - var 1 * var 3)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δW_0, δW_1, δW_3, δW_4]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 0 * h₂ - ρ 3 * h₁)

/-! ## The Jacobi equation

Variables: `0 = z`, `1 = t`, `2 = n`, `3 = α`, `4 = β`, `5 = Y₀`, `6 = Y₁`, `7 = Y₂`. -/

/-- The derivation `d/dz = −2 d/dt` on functions of `t`. -/
def δJ : Fin 8 → ZExp 8
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -2
  | ⟨5, _⟩ => -(2 * var 6)
  | ⟨6, _⟩ => -(2 * var 7)
  | _ => 0

theorem δJ_0 : δJ 0 = 1 := rfl
theorem δJ_1 : δJ 1 = -2 := rfl
theorem δJ_2 : δJ 2 = 0 := rfl
theorem δJ_3 : δJ 3 = 0 := rfl
theorem δJ_4 : δJ 4 = 0 := rfl
theorem δJ_5 : δJ 5 = -(2 * var 6) := rfl
theorem δJ_6 : δJ 6 = -(2 * var 7) := rfl

/-- `thm:jacobi`: under `2z = 1 − t` the hypergeometric operator with `a = −n`,
`b = n + α + β + 1`, `c = α + 1` is the Jacobi operator. -/
theorem jacobi_equation :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(2 * var 0, 1 - var 1)]
        (Lh δJ (var 0) (-(var 2)) (var 2 + var 3 + var 4 + 1) (var 3 + 1) (var 5),
          (1 - var 1 * var 1) * var 7 + (var 4 - var 3 - (var 3 + var 4 + 2) * var 1) * var 6 +
            var 2 * (var 2 + var 3 + var 4 + 1) * var 5)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Lh, δJ_0, δJ_1, δJ_2, δJ_3, δJ_4, δJ_5, δJ_6]
    linear_combination ((ρ 6)*(ρ 3) + (ρ 6)*(ρ 4) + 2*(ρ 6) + (ρ 7)*(ρ 1) - 2*(ρ 7)*(ρ 0) + (ρ 7)) * h)

/-! ## The normal form `u″ + Q u = 0`

Variables: `0 = z`, `1 = γ`, `2 = σ`, `3 = ab`, `4 = t`, `5 = u`, `6 = m`, `7 = U₀`, `8 = U₁`, `9 = U₂`,
with `c = 2γ`, `a + b + 1 = 2σ`, so that `P/2 = (γ − σ z)/(z (1 − z))`; `t` stands for `1/z` and `u` for
`1/(1 − z)`; `m` is the gauge factor with `m′ = −(P/2) m`. -/

/-- The derivation for the gauge substitution `y = m U`. -/
def δQ : Fin 10 → ZExp 10
  | ⟨0, _⟩ => 1
  | ⟨4, _⟩ => -(var 4 * var 4)
  | ⟨5, _⟩ => var 5 * var 5
  | ⟨6, _⟩ => -((var 1 - var 2 * var 0) * var 4 * var 5 * var 6)
  | ⟨7, _⟩ => var 8
  | ⟨8, _⟩ => var 9
  | _ => 0

theorem δQ_0 : δQ 0 = 1 := rfl
theorem δQ_1 : δQ 1 = 0 := rfl
theorem δQ_2 : δQ 2 = 0 := rfl
theorem δQ_3 : δQ 3 = 0 := rfl
theorem δQ_4 : δQ 4 = -(var 4 * var 4) := rfl
theorem δQ_5 : δQ 5 = var 5 * var 5 := rfl
theorem δQ_6 : δQ 6 = -((var 1 - var 2 * var 0) * var 4 * var 5 * var 6) := rfl
theorem δQ_7 : δQ 7 = var 8 := rfl
theorem δQ_8 : δQ 8 = var 9 := rfl
theorem δQ_9 : δQ 9 = 0 := rfl

/-- `prop:q-form` as a formal differential identity: for `y = m U`,
`4z(1 − z) · (z(1 − z) y″ + (c − (a + b + 1) z) y′ − ab y) = m · (4z²(1 − z)² U″ + N(z) U)`, where
`N(z) = z² (1 − (a − b)²) + z (2c (a + b − 1) − 4ab) + c (2 − c)` is the printed numerator of `Q`
(written with `c = 2γ`, `a + b + 1 = 2σ`, `(a − b)² = (2σ − 1)² − 4ab`). -/
theorem q_form_formal :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [(var 4 * var 0, 1), (var 5 * (1 - var 0), 1)]
        (4 * var 0 * (1 - var 0) *
            (var 0 * (1 - var 0) * der δQ (der δQ (var 6 * var 7)) +
              (2 * var 1 - 2 * var 2 * var 0) * der δQ (var 6 * var 7) - var 3 * (var 6 * var 7)),
          var 6 *
            (4 * (var 0 * var 0) * ((1 - var 0) * (1 - var 0)) * var 9 +
              (var 0 * var 0 * (1 - (2 * var 2 - 1) * (2 * var 2 - 1) + 4 * var 3) +
                  var 0 * (4 * var 1 * (2 * var 2 - 2) - 4 * var 3) + 2 * var 1 * (2 - 2 * var 1)) *
                var 7))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δQ_0, δQ_1, δQ_2, δQ_3, δQ_4, δQ_5, δQ_6, δQ_7, δQ_8, δQ_9]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (4*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 4)*(ρ 5)^2*(ρ 0)^3 - 8*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 4)*(ρ 5)^2*(ρ 0)^2 + 4*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 4)*(ρ 5)^2*(ρ 0) + 4*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5)^2*(ρ 0)^2 - 8*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5)^2*(ρ 0) + 4*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5)^2 + 8*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5)*(ρ 0) - 8*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5) - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 4)*(ρ 5)^2*(ρ 0)^4 + 16*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 4)*(ρ 5)^2*(ρ 0)^3 - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 4)*(ρ 5)^2*(ρ 0)^2 - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)^2*(ρ 0)^3 + 16*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)^2*(ρ 0)^2 - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)^2*(ρ 0) - 16*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^2 + 16*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0) + 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 4)*(ρ 5)*(ρ 0)^3 - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 4)*(ρ 5)*(ρ 0)^2 + 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 4)*(ρ 5)*(ρ 0) - 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)^2*(ρ 0)^3 + 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)^2*(ρ 0)^2 - 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)^2*(ρ 0) + 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0)^2 - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0) + 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5) + 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 4)*(ρ 5)^2*(ρ 0)^5 - 8*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 4)*(ρ 5)^2*(ρ 0)^4 + 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 4)*(ρ 5)^2*(ρ 0)^3 + 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)^2*(ρ 0)^4 - 8*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)^2*(ρ 0)^3 + 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)^2*(ρ 0)^2 + 8*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)*(ρ 0)^3 - 8*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)*(ρ 0)^2 - 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 4)*(ρ 5)*(ρ 0)^4 + 8*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 4)*(ρ 5)*(ρ 0)^3 - 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 4)*(ρ 5)*(ρ 0)^2 + 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 5)^2*(ρ 0)^4 - 8*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 5)^2*(ρ 0)^3 + 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 5)^2*(ρ 0)^2 - 8*(ρ 8)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0)^3 + 16*(ρ 8)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0)^2 - 8*(ρ 8)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0) + 8*(ρ 8)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^4 - 16*(ρ 8)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^3 + 8*(ρ 8)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^2) * h₁ +
      (-4*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5)*(ρ 0) + 4*(ρ 7)*(ρ 1)^2*(ρ 6)*(ρ 5) - 4*(ρ 7)*(ρ 1)^2*(ρ 6) + 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^2 - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0) + 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 2)*(ρ 0) + 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0)^2 - 4*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 5)*(ρ 0) - 8*(ρ 7)*(ρ 1)*(ρ 6)*(ρ 0) + 4*(ρ 7)*(ρ 1)*(ρ 6) - 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)*(ρ 0)^3 + 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 5)*(ρ 0)^2 - 4*(ρ 7)*(ρ 6)*(ρ 2)^2*(ρ 0)^2 - 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^3 + 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 5)*(ρ 0)^2 + 4*(ρ 7)*(ρ 6)*(ρ 2)*(ρ 0)^2 + 8*(ρ 8)*(ρ 1)*(ρ 6)*(ρ 0)^2 - 8*(ρ 8)*(ρ 1)*(ρ 6)*(ρ 0) - 8*(ρ 8)*(ρ 6)*(ρ 2)*(ρ 0)^3 + 8*(ρ 8)*(ρ 6)*(ρ 2)*(ρ 0)^2) * h₂)

end LeanProofs.IPRA.Analysis.HypergeometricOdeFormal
