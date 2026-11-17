import IPRADerivations.DiophantineNumberTheory.FermatQuarticPoints

/-!
# Rational right triangles with square area

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:fermat-area` and
Corollaries `cor:quartic-obstruction`, `cor:square-progression`. The integer core — no positive
`a, b, c, s` with `a² + b² = c²`, `ab = 2s²` — is `SquareArea.square_area`
(`FermatQuarticPoints.no_square_area`); here are the consequences the packet draws from it.

* `rational_square_area` (`thm:fermat-area`, rational form): no positive rationals
  `a₁/a₂, b₁/b₂, c₁/c₂` and nonzero `q₁/q₂` with `(a₁/a₂)² + (b₁/b₂)² = (c₁/c₂)²` and
  `(a₁/a₂)(b₁/b₂)/2 = (q₁/q₂)²`, cleared as
  `a₁² b₂² c₂² + b₁² a₂² c₂² = c₁² a₂² b₂²` and `a₁ b₁ q₂² = 2 q₁² a₂ b₂`. Multiplying by the product of
  the denominators `L = a₂ b₂ c₂ q₂` gives the integer triangle
  `(a₁ b₂ c₂ q₂, b₁ a₂ c₂ q₂, c₁ a₂ b₂ q₂; q₁ a₂ b₂ c₂)`;
* `no_area_one`: in particular no rational right triangle has area `1`;
* `quartic_obstruction` (`cor:quartic-obstruction`): no positive `x, y, z` with `x⁴ − y⁴ = z²`, and
  no positive `a, b, c` with `a⁴ + b⁴ = c⁴` (`c⁴ − a⁴ = (b²)²`);
* `square_progression` (`cor:square-progression`): no `R, S, T, D` with `D ≥ 1` and
  `S² − R² = T² − S² = D²` (the equations are homogeneous, so this is the rational statement after
  clearing a common denominator): `(T − R, T + R; 2S)` is a right triangle of area `D²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.RationalTriangles

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuarticPoints (no_square_area fourth_difference)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (q4)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `thm:fermat-area`, rational form, with the denominators cleared. -/
theorem rational_square_area {a₁ a₂ b₁ b₂ c₁ c₂ q₁ q₂ : PTm n}
    (ha₁ : Γ ⊢[PRAAx] a₁ ≐ succ (pred a₁)) (ha₂ : Γ ⊢[PRAAx] a₂ ≐ succ (pred a₂))
    (hb₁ : Γ ⊢[PRAAx] b₁ ≐ succ (pred b₁)) (hb₂ : Γ ⊢[PRAAx] b₂ ≐ succ (pred b₂))
    (hc₂ : Γ ⊢[PRAAx] c₂ ≐ succ (pred c₂))
    (hq₁ : Γ ⊢[PRAAx] q₁ ≐ succ (pred q₁)) (hq₂ : Γ ⊢[PRAAx] q₂ ≐ succ (pred q₂))
    (h₁ : Γ ⊢[PRAAx] a₁ * a₁ * (b₂ * b₂) * (c₂ * c₂) + b₁ * b₁ * (a₂ * a₂) * (c₂ * c₂) ≐
      c₁ * c₁ * (a₂ * a₂) * (b₂ * b₂))
    (h₂ : Γ ⊢[PRAAx] a₁ * b₁ * (q₂ * q₂) ≐ two * (q₁ * q₁) * (a₂ * b₂)) : Γ ⊢[PRAAx] Fm.bot := by
  have e₁ := natEq h₁; have e₂ := natEq h₂
  refine no_square_area (a := a₁ * b₂ * c₂ * q₂) (b := b₁ * a₂ * c₂ * q₂) (c := c₁ * a₂ * b₂ * q₂)
    (s := q₁ * a₂ * b₂ * c₂)
    (pos_mul (pos_mul (pos_mul ha₁ hb₂) hc₂) hq₂) (pos_mul (pos_mul (pos_mul hb₁ ha₂) hc₂) hq₂)
    (pos_mul (pos_mul (pos_mul hq₁ ha₂) hb₂) hc₂) ?_ ?_
  · apply deriveNat; ipra_simps
    linear_combination (𝔞 q₂ * 𝔞 q₂) * e₁
  · apply deriveNat; ipra_simps
    linear_combination (𝔞 a₂ * 𝔞 b₂ * 𝔞 c₂ * 𝔞 c₂) * e₂

/-- No rational right triangle has area `1`: `(a₁/a₂)(b₁/b₂) = 2`. -/
theorem no_area_one {a₁ a₂ b₁ b₂ c₁ c₂ : PTm n}
    (ha₁ : Γ ⊢[PRAAx] a₁ ≐ succ (pred a₁)) (ha₂ : Γ ⊢[PRAAx] a₂ ≐ succ (pred a₂))
    (hb₁ : Γ ⊢[PRAAx] b₁ ≐ succ (pred b₁)) (hb₂ : Γ ⊢[PRAAx] b₂ ≐ succ (pred b₂))
    (hc₂ : Γ ⊢[PRAAx] c₂ ≐ succ (pred c₂))
    (h₁ : Γ ⊢[PRAAx] a₁ * a₁ * (b₂ * b₂) * (c₂ * c₂) + b₁ * b₁ * (a₂ * a₂) * (c₂ * c₂) ≐
      c₁ * c₁ * (a₂ * a₂) * (b₂ * b₂))
    (h₂ : Γ ⊢[PRAAx] a₁ * b₁ ≐ two * (a₂ * b₂)) : Γ ⊢[PRAAx] Fm.bot := by
  have one_pos : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  refine rational_square_area (q₁ := one) (q₂ := one) ha₁ ha₂ hb₁ hb₂ hc₂ one_pos one_pos h₁ ?_
  have e := natEq h₂
  apply deriveNat; ipra_simps
  linear_combination e

/-- `cor:quartic-obstruction`: `x⁴ − y⁴ = z²` has no positive solutions. -/
theorem quartic_obstruction {x y z : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hy : Γ ⊢[PRAAx] y ≐ succ (pred y))
    (hz : Γ ⊢[PRAAx] z ≐ succ (pred z)) (h : Γ ⊢[PRAAx] q4 y + z * z ≐ q4 x) : Γ ⊢[PRAAx] Fm.bot :=
  fourth_difference hx hy hz h

/-- `cor:quartic-obstruction`, second part: `a⁴ + b⁴ = c⁴` has no positive solutions (`c⁴ − a⁴ = (b²)²`). -/
theorem quartic_fermat {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (h : Γ ⊢[PRAAx] q4 a + q4 b ≐ q4 c) : Γ ⊢[PRAAx] Fm.bot :=
  fourth_difference (z := b * b) hc ha (pos_mul hb hb) h

/-- `cor:square-progression`: no `R, S, T` and `D ≥ 1` with `R² + D² = S²` and `S² + D² = T²`. -/
theorem square_progression {R S T D : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (h₁ : Γ ⊢[PRAAx] R * R + D * D ≐ S * S) (h₂ : Γ ⊢[PRAAx] S * S + D * D ≐ T * T) : Γ ⊢[PRAAx] Fm.bot := by
  have e₁ := natEq h₁; have e₂ := natEq h₂; have d := natEq hD
  -- `T > R`, since `T² = R² + 2 D² > R²`.
  have big : Γ ⊢[PRAAx] le (succ (R * R)) (T * T) := by
    refine le_of_eq_add (d := two * (pred D * pred D) + two * pred D + two * pred D + one) ?_
    apply deriveNat; ipra_simps
    linear_combination -e₂ - e₁ + 2 * (𝔞 D + 𝔞 (pred D) + 1) * d
  refine .orE (lt_or_le R T) ?_ ?_
  · let C := lt R T :: Γ
    have e := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] lt R T))
    have f₁ := natEq (h₁.wk : C ⊢[PRAAx] _); have f₂ := natEq (h₂.wk : C ⊢[PRAAx] _)
    refine no_square_area (a := succ (monus T (succ R))) (b := T + R) (c := two * S) (s := D)
      (congrSucc (pred_succ _).eqSymm) ?_ hD.wk ?_ ?_
    · have p : C ⊢[PRAAx] T + R ≐ succ (R + monus T (succ R) + R) := by
        apply deriveNat; ipra_simps; linear_combination e
      exact AnalyticNumberTheory.Primes.eq_succ_pred p
    · apply deriveNat; ipra_simps
      linear_combination 2 * f₁ - 2 * f₂ - (𝔞 (monus T (succ R)) + 1 + 𝔞 T - 𝔞 R) * e
    · apply deriveNat; ipra_simps
      linear_combination -f₁ - f₂ - (𝔞 T + 𝔞 R) * e
  · let C := le T R :: Γ
    have sq : C ⊢[PRAAx] le (T * T) (R * R) := AnalyticNumberTheory.PhiLower.le_mul_mono Prf.hyp0 Prf.hyp0
    exact not_succ_le_self (R * R) _ (le_trans big.wk sq)

end LeanProofs.IPRA.DiophantineNumberTheory.RationalTriangles
