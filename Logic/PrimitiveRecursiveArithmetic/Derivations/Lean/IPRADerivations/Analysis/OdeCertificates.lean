import IPRADerivations.Core.Integers

/-!
# Algebraic certificates for the hypergeometric equation: Wronskian and Jacobi substitution

Packet: `analysis/hypergeometric_ipra_2026-11-16`:

* Lemma `lem:wronskian` (`sections/05_ode.tex`): "For an equation `y″ + P y′ + Q y = 0`, direct expansion
  gives `W′ = −P W`. Here `P(z) = (c − (a + b + 1) z)/(z (1 − z)) = c/z + (c − a − b − 1)/(1 − z)`";
* Theorem `thm:jacobi` (`sections/06_special.tex`): "Substitute `z = (1 − t)/2` into the hypergeometric
  ODE. Clearing denominators yields
  `(1 − t²) y″ + [β − α − (α + β + 2) t] y′ + n (n + α + β + 1) y = 0`, the Jacobi equation", for
  `a = −n`, `b = n + α + β + 1`, `c = α + 1` (the Legendre case is `α = β = 0`).

With signed integer terms:

* `wronskian`: if `y₁″ + P y₁′ + Q y₁ = 0` and `y₂″ + P y₂′ + Q y₂ = 0`, then
  `y₁ y₂″ − y₁″ y₂ = −P (y₁ y₂′ − y₁′ y₂)`; the left side is `W′` by the product rule (the mixed terms
  `y₁′ y₂′` cancel);
* `partial_fractions`: `c (1 − z) + (c − a − b − 1) z = c − (a + b + 1) z`;
* `jacobi_leading`: `2z = 1 − t` gives `4 z (1 − z) = (1 − t)(1 + t)`, the coefficient of `y″`
  (`d²/dz² = 4 d²/dt²`);
* `jacobi_first`: `2z = 1 − t` gives
  `−2 ((α + 1) − ((−n) + (n + α + β + 1) + 1) z) = β − α − (α + β + 2) t`, the coefficient of `y′`
  (`d/dz = −2 d/dt`);
* `jacobi_zero`: `−((−n)(n + α + β + 1)) = n (n + α + β + 1)`.

The differential calculus (derivatives of named functions and the chain rule) is the reading of these
identities and is not formalized.
-/

namespace LeanProofs.IPRA.Analysis.OdeCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `lem:wronskian`: `W′ = −P W` for two solutions of `y″ + P y′ + Q y = 0`. -/
theorem wronskian {y₁ d₁ e₁ y₂ d₂ e₂ P Qc : ZT n}
    (h₁ : Γ ⊢[PRAAx] ZT.eq (e₁ + P * d₁ + Qc * y₁) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (e₂ + P * d₂ + Qc * y₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (y₁ * e₂ - e₁ * y₂) (-(P * (y₁ * d₂ - d₁ * y₂))) := by
  have a₁ := ZT.toZ_eq h₁
  have a₂ := ZT.toZ_eq h₂
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit] at a₁ a₂ ⊢
  push_cast at a₁ a₂ ⊢
  linear_combination ZT.toZ Γ y₁ * a₂ - ZT.toZ Γ y₂ * a₁

/-- `P = c/z + (c − a − b − 1)/(1 − z)`, cleared of denominators. -/
theorem partial_fractions (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (c * (ZT.natLit 1 - z) + (c - a - b - ZT.natLit 1) * z)
      (c - (a + b + ZT.natLit 1) * z) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit]
    push_cast
    ring)

/-- `thm:jacobi`, the coefficient of `y″`: `2z = 1 − t` gives `4 z (1 − z) = (1 − t)(1 + t)`. -/
theorem jacobi_leading {z t : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * z) (ZT.natLit 1 - t)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * (z * (ZT.natLit 1 - z)))
      ((ZT.natLit 1 - t) * (ZT.natLit 1 + t)) := by
  have a := ZT.toZ_eq h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit] at a ⊢
  push_cast at a ⊢
  linear_combination (1 - 2 * ZT.toZ Γ z + ZT.toZ Γ t) * a

/-- `thm:jacobi`, the coefficient of `y′`. -/
theorem jacobi_first {z t : ZT n} (m α β : ZT n)
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * z) (ZT.natLit 1 - t)) :
    Γ ⊢[PRAAx] ZT.eq
      (-(ZT.natLit 2 * ((α + ZT.natLit 1) - ((-m) + (m + α + β + ZT.natLit 1) + ZT.natLit 1) * z)))
      (β - α - (α + β + ZT.natLit 2) * t) := by
  have a := ZT.toZ_eq h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit] at a ⊢
  push_cast at a ⊢
  linear_combination (ZT.toZ Γ α + ZT.toZ Γ β + 2) * a

/-- `thm:jacobi`, the coefficient of `y`. -/
theorem jacobi_zero (m α β : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (-((-m) * (m + α + β + ZT.natLit 1))) (m * (m + α + β + ZT.natLit 1)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

end LeanProofs.IPRA.Analysis.OdeCertificates
