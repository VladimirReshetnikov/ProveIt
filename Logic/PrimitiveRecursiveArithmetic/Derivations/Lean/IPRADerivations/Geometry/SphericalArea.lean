import IPRADerivations.Geometry.SphericalHalf

/-!
# The algebraic solid-angle identity and L'Huilier's formula

Packet: `spherical_trigonometry_ipra_2026-11-15`, `sections/10_area.tex`: the polynomial identity
(10.9) and Corollary `cor:lhuillier` (10.14), cross-multiplied.

* `gram_DQ` (10.9): with `x = cos a`, `y = cos b`, `z = cos c`, `D = 1 + x + y + z` and the Gram
  relation `τ² = 1 + 2xyz − x² − y² − z²`, `D² + τ² = 2(1 + x)(1 + y)(1 + z)`;
* `lhuilierR`, `lhuilier` (10.14), cross-multiplied: with the quarter sides `a/4, b/4, c/4` as unit
  pairs, `Q = 4 cos(a/2) cos(b/2) cos(c/2)` and `D = 1 + cos a + cos b + cos c`,
  `(Q − D) · ∏ cos(·) = (Q + D) · ∏ sin(·)` over the four quarter angles `p/2`, `(p − a)/2`,
  `(p − b)/2`, `(p − c)/2`, i.e. `(Q − D)/(Q + D) = tan(p/2) tan((p − a)/2) tan((p − b)/2) tan((p − c)/2)`,
  which with (10.15) is `tan²(E/4) = ∏ tan(·)`. The certificate modulo the three unit relations was
  computed by polynomial reduction.

The solid-angle formulas (10.10)–(10.13), Girard's theorem and the positive roots are not
formalized.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace LeanProofs.IPRA.Geometry.SphericalArea

open_ipra
open LeanProofs.IPRA.Geometry.SphericalHalf (sin3R cos3R sin3 cos3 toZ_sin3 toZ_cos3)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- (10.9): `D² + τ² = 2(1 + x)(1 + y)(1 + z)` from the Gram relation. -/
theorem gram_DQ {x y z τ : ZT n}
    (g : Γ ⊢[PRAAx] ZT.eq (τ * τ) (ZT.natLit 1 + ZT.natLit 2 * x * y * z - x * x - y * y - z * z)) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 + x + y + z) * (ZT.natLit 1 + x + y + z) + τ * τ)
      (ZT.natLit 2 * (ZT.natLit 1 + x) * (ZT.natLit 1 + y) * (ZT.natLit 1 + z)) := by
  have e := ZT.toZ_eq g
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at e ⊢
  push_cast at e ⊢
  linear_combination e

section Ring

variable {R : Type*} [CommRing R]

/-- L'Huilier's identity over a commutative ring, in quarter-side unit pairs. -/
theorem lhuilierR (s₁ c₁ s₂ c₂ s₃ c₃ : R) (u₁ : s₁ * s₁ + c₁ * c₁ = 1) (u₂ : s₂ * s₂ + c₂ * c₂ = 1)
    (u₃ : s₃ * s₃ + c₃ * c₃ = 1) :
    (4 * (c₁ * c₁ - s₁ * s₁) * (c₂ * c₂ - s₂ * s₂) * (c₃ * c₃ - s₃ * s₃) -
        (1 + ((c₁ * c₁ - s₁ * s₁) ^ 2 - (2 * s₁ * c₁) ^ 2) + ((c₂ * c₂ - s₂ * s₂) ^ 2 - (2 * s₂ * c₂) ^ 2) +
          ((c₃ * c₃ - s₃ * s₃) ^ 2 - (2 * s₃ * c₃) ^ 2))) *
      (cos3R s₁ c₁ s₂ c₂ s₃ c₃ * cos3R (-s₁) c₁ s₂ c₂ s₃ c₃ * cos3R s₁ c₁ (-s₂) c₂ s₃ c₃ *
        cos3R s₁ c₁ s₂ c₂ (-s₃) c₃) =
    (4 * (c₁ * c₁ - s₁ * s₁) * (c₂ * c₂ - s₂ * s₂) * (c₃ * c₃ - s₃ * s₃) +
        (1 + ((c₁ * c₁ - s₁ * s₁) ^ 2 - (2 * s₁ * c₁) ^ 2) + ((c₂ * c₂ - s₂ * s₂) ^ 2 - (2 * s₂ * c₂) ^ 2) +
          ((c₃ * c₃ - s₃ * s₃) ^ 2 - (2 * s₃ * c₃) ^ 2))) *
      (sin3R s₁ c₁ s₂ c₂ s₃ c₃ * sin3R (-s₁) c₁ s₂ c₂ s₃ c₃ * sin3R s₁ c₁ (-s₂) c₂ s₃ c₃ *
        sin3R s₁ c₁ s₂ c₂ (-s₃) c₃) := by
  simp only [sin3R, cos3R]
  linear_combination (-c₁^6*c₂^4*c₃^4 + c₁^6*c₂^4*s₃^4 + c₁^6*c₃^4*s₂^4 - c₁^6*s₂^4*s₃^4 + 4*c₁^4*c₂^6*c₃^6 - 4*c₁^4*c₂^6*c₃^4*s₃^2 + 4*c₁^4*c₂^6*c₃^2*s₃^4 - 4*c₁^4*c₂^6*s₃^6 - 4*c₁^4*c₂^4*c₃^6*s₂^2 + 7*c₁^4*c₂^4*c₃^4*s₁^2 - 12*c₁^4*c₂^4*c₃^4*s₂^2*s₃^2 - c₁^4*c₂^4*c₃^4 + 12*c₁^4*c₂^4*c₃^2*s₂^2*s₃^4 - 7*c₁^4*c₂^4*s₁^2*s₃^4 + 4*c₁^4*c₂^4*s₂^2*s₃^6 + c₁^4*c₂^4*s₃^4 + 4*c₁^4*c₂^2*c₃^6*s₂^4 + 12*c₁^4*c₂^2*c₃^4*s₂^4*s₃^2 - 12*c₁^4*c₂^2*c₃^2*s₂^4*s₃^4 - 4*c₁^4*c₂^2*s₂^4*s₃^6 - 4*c₁^4*c₃^6*s₂^6 - 7*c₁^4*c₃^4*s₁^2*s₂^4 + 4*c₁^4*c₃^4*s₂^6*s₃^2 + c₁^4*c₃^4*s₂^4 - 4*c₁^4*c₃^2*s₂^6*s₃^4 + 7*c₁^4*s₁^2*s₂^4*s₃^4 + 4*c₁^4*s₂^6*s₃^6 - c₁^4*s₂^4*s₃^4 - c₁^2*c₂^8*c₃^4 + c₁^2*c₂^8*s₃^4 - 8*c₁^2*c₂^6*c₃^6*s₁^2 + 4*c₁^2*c₂^6*c₃^6 - 8*c₁^2*c₂^6*c₃^4*s₁^2*s₃^2 + 6*c₁^2*c₂^6*c₃^4*s₂^2 - 4*c₁^2*c₂^6*c₃^4*s₃^2 + 8*c₁^2*c₂^6*c₃^2*s₁^2*s₃^4 + 4*c₁^2*c₂^6*c₃^2*s₃^4 + 8*c₁^2*c₂^6*s₁^2*s₃^6 - 6*c₁^2*c₂^6*s₂^2*s₃^4 - 4*c₁^2*c₂^6*s₃^6 - c₁^2*c₂^4*c₃^8 - 8*c₁^2*c₂^4*c₃^6*s₁^2*s₂^2 - 4*c₁^2*c₂^4*c₃^6*s₂^2 + 6*c₁^2*c₂^4*c₃^6*s₃^2 - 7*c₁^2*c₂^4*c₃^4*s₁^4 - 8*c₁^2*c₂^4*c₃^4*s₁^2*s₂^2*s₃^2 + 8*c₁^2*c₂^4*c₃^4*s₁^2 - 12*c₁^2*c₂^4*c₃^4*s₂^2*s₃^2 - 2*c₁^2*c₂^4*c₃^4 + 8*c₁^2*c₂^4*c₃^2*s₁^2*s₂^2*s₃^4 + 12*c₁^2*c₂^4*c₃^2*s₂^2*s₃^4 - 6*c₁^2*c₂^4*c₃^2*s₃^6 + 7*c₁^2*c₂^4*s₁^4*s₃^4 + 8*c₁^2*c₂^4*s₁^2*s₂^2*s₃^6 - 8*c₁^2*c₂^4*s₁^2*s₃^4 + 4*c₁^2*c₂^4*s₂^2*s₃^6 + c₁^2*c₂^4*s₃^8 + 2*c₁^2*c₂^4*s₃^4 + 8*c₁^2*c₂^2*c₃^6*s₁^2*s₂^4 + 4*c₁^2*c₂^2*c₃^6*s₂^4 + 8*c₁^2*c₂^2*c₃^4*s₁^2*s₂^4*s₃^2 - 6*c₁^2*c₂^2*c₃^4*s₂^6 + 12*c₁^2*c₂^2*c₃^4*s₂^4*s₃^2 - 8*c₁^2*c₂^2*c₃^2*s₁^2*s₂^4*s₃^4 - 12*c₁^2*c₂^2*c₃^2*s₂^4*s₃^4 - 8*c₁^2*c₂^2*s₁^2*s₂^4*s₃^6 + 6*c₁^2*c₂^2*s₂^6*s₃^4 - 4*c₁^2*c₂^2*s₂^4*s₃^6 + c₁^2*c₃^8*s₂^4 + 8*c₁^2*c₃^6*s₁^2*s₂^6 - 4*c₁^2*c₃^6*s₂^6 - 6*c₁^2*c₃^6*s₂^4*s₃^2 + 7*c₁^2*c₃^4*s₁^4*s₂^4 + 8*c₁^2*c₃^4*s₁^2*s₂^6*s₃^2 - 8*c₁^2*c₃^4*s₁^2*s₂^4 + c₁^2*c₃^4*s₂^8 + 4*c₁^2*c₃^4*s₂^6*s₃^2 + 2*c₁^2*c₃^4*s₂^4 - 8*c₁^2*c₃^2*s₁^2*s₂^6*s₃^4 - 4*c₁^2*c₃^2*s₂^6*s₃^4 + 6*c₁^2*c₃^2*s₂^4*s₃^6 - 7*c₁^2*s₁^4*s₂^4*s₃^4 - 8*c₁^2*s₁^2*s₂^6*s₃^6 + 8*c₁^2*s₁^2*s₂^4*s₃^4 - c₁^2*s₂^8*s₃^4 + 4*c₁^2*s₂^6*s₃^6 - c₁^2*s₂^4*s₃^8 - 2*c₁^2*s₂^4*s₃^4 + c₂^8*c₃^4*s₁^2 - c₂^8*c₃^4 - c₂^8*s₁^2*s₃^4 + c₂^8*s₃^4 + 12*c₂^6*c₃^6*s₁^4 - 12*c₂^6*c₃^6*s₁^2 + 4*c₂^6*c₃^6 + 20*c₂^6*c₃^4*s₁^4*s₃^2 - 6*c₂^6*c₃^4*s₁^2*s₂^2 - 4*c₂^6*c₃^4*s₁^2*s₃^2 + 6*c₂^6*c₃^4*s₂^2 - 4*c₂^6*c₃^4*s₃^2 - 20*c₂^6*c₃^2*s₁^4*s₃^4 + 4*c₂^6*c₃^2*s₁^2*s₃^4 + 4*c₂^6*c₃^2*s₃^4 - 12*c₂^6*s₁^4*s₃^6 + 6*c₂^6*s₁^2*s₂^2*s₃^4 + 12*c₂^6*s₁^2*s₃^6 - 6*c₂^6*s₂^2*s₃^4 - 4*c₂^6*s₃^6 + c₂^4*c₃^8*s₁^2 - c₂^4*c₃^8 + 20*c₂^4*c₃^6*s₁^4*s₂^2 - 4*c₂^4*c₃^6*s₁^2*s₂^2 - 6*c₂^4*c₃^6*s₁^2*s₃^2 - 4*c₂^4*c₃^6*s₂^2 + 6*c₂^4*c₃^6*s₃^2 + c₂^4*c₃^4*s₁^6 + 28*c₂^4*c₃^4*s₁^4*s₂^2*s₃^2 - 15*c₂^4*c₃^4*s₁^4 + 4*c₂^4*c₃^4*s₁^2*s₂^2*s₃^2 + 10*c₂^4*c₃^4*s₁^2 - 12*c₂^4*c₃^4*s₂^2*s₃^2 - 2*c₂^4*c₃^4 - 28*c₂^4*c₃^2*s₁^4*s₂^2*s₃^4 - 4*c₂^4*c₃^2*s₁^2*s₂^2*s₃^4 + 6*c₂^4*c₃^2*s₁^2*s₃^6 + 12*c₂^4*c₃^2*s₂^2*s₃^4 - 6*c₂^4*c₃^2*s₃^6 - c₂^4*s₁^6*s₃^4 - 20*c₂^4*s₁^4*s₂^2*s₃^6 + 15*c₂^4*s₁^4*s₃^4 + 4*c₂^4*s₁^2*s₂^2*s₃^6 - c₂^4*s₁^2*s₃^8 - 10*c₂^4*s₁^2*s₃^4 + 4*c₂^4*s₂^2*s₃^6 + c₂^4*s₃^8 + 2*c₂^4*s₃^4 - 20*c₂^2*c₃^6*s₁^4*s₂^4 + 4*c₂^2*c₃^6*s₁^2*s₂^4 + 4*c₂^2*c₃^6*s₂^4 - 28*c₂^2*c₃^4*s₁^4*s₂^4*s₃^2 + 6*c₂^2*c₃^4*s₁^2*s₂^6 - 4*c₂^2*c₃^4*s₁^2*s₂^4*s₃^2 - 6*c₂^2*c₃^4*s₂^6 + 12*c₂^2*c₃^4*s₂^4*s₃^2 + 28*c₂^2*c₃^2*s₁^4*s₂^4*s₃^4 + 4*c₂^2*c₃^2*s₁^2*s₂^4*s₃^4 - 12*c₂^2*c₃^2*s₂^4*s₃^4 + 20*c₂^2*s₁^4*s₂^4*s₃^6 - 6*c₂^2*s₁^2*s₂^6*s₃^4 - 4*c₂^2*s₁^2*s₂^4*s₃^6 + 6*c₂^2*s₂^6*s₃^4 - 4*c₂^2*s₂^4*s₃^6 - c₃^8*s₁^2*s₂^4 + c₃^8*s₂^4 - 12*c₃^6*s₁^4*s₂^6 + 12*c₃^6*s₁^2*s₂^6 + 6*c₃^6*s₁^2*s₂^4*s₃^2 - 4*c₃^6*s₂^6 - 6*c₃^6*s₂^4*s₃^2 - c₃^4*s₁^6*s₂^4 - 20*c₃^4*s₁^4*s₂^6*s₃^2 + 15*c₃^4*s₁^4*s₂^4 - c₃^4*s₁^2*s₂^8 + 4*c₃^4*s₁^2*s₂^6*s₃^2 - 10*c₃^4*s₁^2*s₂^4 + c₃^4*s₂^8 + 4*c₃^4*s₂^6*s₃^2 + 2*c₃^4*s₂^4 + 20*c₃^2*s₁^4*s₂^6*s₃^4 - 4*c₃^2*s₁^2*s₂^6*s₃^4 - 6*c₃^2*s₁^2*s₂^4*s₃^6 - 4*c₃^2*s₂^6*s₃^4 + 6*c₃^2*s₂^4*s₃^6 + s₁^6*s₂^4*s₃^4 + 12*s₁^4*s₂^6*s₃^6 - 15*s₁^4*s₂^4*s₃^4 + s₁^2*s₂^8*s₃^4 - 12*s₁^2*s₂^6*s₃^6 + s₁^2*s₂^4*s₃^8 + 10*s₁^2*s₂^4*s₃^4 - s₂^8*s₃^4 + 4*s₂^6*s₃^6 - s₂^4*s₃^8 - 2*s₂^4*s₃^4) * u₁ +
    (2*c₂^6*c₃^4*s₁^2 - c₂^6*c₃^4 - 2*c₂^6*s₁^2*s₃^4 + c₂^6*s₃^4 - 16*c₂^4*c₃^6*s₁^6 + 24*c₂^4*c₃^6*s₁^4 - 16*c₂^4*c₃^6*s₁^2 + 4*c₂^4*c₃^6 - 16*c₂^4*c₃^4*s₁^6*s₃^2 + 24*c₂^4*c₃^4*s₁^4*s₃^2 - 14*c₂^4*c₃^4*s₁^2*s₂^2 + 2*c₂^4*c₃^4*s₁^2 + 7*c₂^4*c₃^4*s₂^2 - 4*c₂^4*c₃^4*s₃^2 - c₂^4*c₃^4 + 16*c₂^4*c₃^2*s₁^6*s₃^4 - 24*c₂^4*c₃^2*s₁^4*s₃^4 + 4*c₂^4*c₃^2*s₃^4 + 16*c₂^4*s₁^6*s₃^6 - 24*c₂^4*s₁^4*s₃^6 + 14*c₂^4*s₁^2*s₂^2*s₃^4 + 16*c₂^4*s₁^2*s₃^6 - 2*c₂^4*s₁^2*s₃^4 - 7*c₂^4*s₂^2*s₃^4 - 4*c₂^4*s₃^6 + c₂^4*s₃^4 + 2*c₂^2*c₃^8*s₁^2 - c₂^2*c₃^8 - 16*c₂^2*c₃^6*s₁^6 + 24*c₂^2*c₃^6*s₁^4 + 16*c₂^2*c₃^6*s₁^2*s₂^2 - 12*c₂^2*c₃^6*s₁^2*s₃^2 - 16*c₂^2*c₃^6*s₁^2 - 8*c₂^2*c₃^6*s₂^2 + 6*c₂^2*c₃^6*s₃^2 + 4*c₂^2*c₃^6 - 16*c₂^2*c₃^4*s₁^6*s₃^2 + 16*c₂^2*c₃^4*s₁^6 + 24*c₂^2*c₃^4*s₁^4*s₃^2 - 24*c₂^2*c₃^4*s₁^4 + 14*c₂^2*c₃^4*s₁^2*s₂^4 + 16*c₂^2*c₃^4*s₁^2*s₂^2*s₃^2 - 16*c₂^2*c₃^4*s₁^2*s₂^2 + 14*c₂^2*c₃^4*s₁^2 - 7*c₂^2*c₃^4*s₂^4 - 8*c₂^2*c₃^4*s₂^2*s₃^2 + 8*c₂^2*c₃^4*s₂^2 - 4*c₂^2*c₃^4*s₃^2 - 3*c₂^2*c₃^4 + 16*c₂^2*c₃^2*s₁^6*s₃^4 - 24*c₂^2*c₃^2*s₁^4*s₃^4 - 16*c₂^2*c₃^2*s₁^2*s₂^2*s₃^4 + 12*c₂^2*c₃^2*s₁^2*s₃^6 + 8*c₂^2*c₃^2*s₂^2*s₃^4 - 6*c₂^2*c₃^2*s₃^6 + 4*c₂^2*c₃^2*s₃^4 + 16*c₂^2*s₁^6*s₃^6 - 16*c₂^2*s₁^6*s₃^4 - 24*c₂^2*s₁^4*s₃^6 + 24*c₂^2*s₁^4*s₃^4 - 14*c₂^2*s₁^2*s₂^4*s₃^4 - 16*c₂^2*s₁^2*s₂^2*s₃^6 + 16*c₂^2*s₁^2*s₂^2*s₃^4 - 2*c₂^2*s₁^2*s₃^8 + 16*c₂^2*s₁^2*s₃^6 - 14*c₂^2*s₁^2*s₃^4 + 7*c₂^2*s₂^4*s₃^4 + 8*c₂^2*s₂^2*s₃^6 - 8*c₂^2*s₂^2*s₃^4 + c₂^2*s₃^8 - 4*c₂^2*s₃^6 + 3*c₂^2*s₃^4 - 2*c₃^8*s₁^2*s₂^2 + 2*c₃^8*s₁^2 + c₃^8*s₂^2 - c₃^8 + 16*c₃^6*s₁^6*s₂^4 + 16*c₃^6*s₁^6*s₂^2 - 16*c₃^6*s₁^6 - 24*c₃^6*s₁^4*s₂^4 - 24*c₃^6*s₁^4*s₂^2 + 24*c₃^6*s₁^4 - 16*c₃^6*s₁^2*s₂^4 + 12*c₃^6*s₁^2*s₂^2*s₃^2 + 32*c₃^6*s₁^2*s₂^2 - 12*c₃^6*s₁^2*s₃^2 - 16*c₃^6*s₁^2 + 12*c₃^6*s₂^4 - 6*c₃^6*s₂^2*s₃^2 - 12*c₃^6*s₂^2 + 6*c₃^6*s₃^2 + 4*c₃^6 + 16*c₃^4*s₁^6*s₂^4*s₃^2 + 16*c₃^4*s₁^6*s₂^2*s₃^2 - 16*c₃^4*s₁^6*s₂^2 - 16*c₃^4*s₁^6*s₃^2 + 16*c₃^4*s₁^6 - 24*c₃^4*s₁^4*s₂^4*s₃^2 - 24*c₃^4*s₁^4*s₂^2*s₃^2 + 24*c₃^4*s₁^4*s₂^2 + 24*c₃^4*s₁^4*s₃^2 - 24*c₃^4*s₁^4 - 2*c₃^4*s₁^2*s₂^6 - 32*c₃^4*s₁^2*s₂^4*s₃^2 + 30*c₃^4*s₁^2*s₂^4 + 16*c₃^4*s₁^2*s₂^2*s₃^2 - 30*c₃^4*s₁^2*s₂^2 + 14*c₃^4*s₁^2 + c₃^4*s₂^6 + 20*c₃^4*s₂^4*s₃^2 - 15*c₃^4*s₂^4 - 4*c₃^4*s₂^2*s₃^2 + 11*c₃^4*s₂^2 - 4*c₃^4*s₃^2 - 3*c₃^4 - 16*c₃^2*s₁^6*s₂^4*s₃^4 - 16*c₃^2*s₁^6*s₂^2*s₃^4 + 16*c₃^2*s₁^6*s₃^4 + 24*c₃^2*s₁^4*s₂^4*s₃^4 + 24*c₃^2*s₁^4*s₂^2*s₃^4 - 24*c₃^2*s₁^4*s₃^4 + 32*c₃^2*s₁^2*s₂^4*s₃^4 - 12*c₃^2*s₁^2*s₂^2*s₃^6 - 16*c₃^2*s₁^2*s₂^2*s₃^4 + 12*c₃^2*s₁^2*s₃^6 - 20*c₃^2*s₂^4*s₃^4 + 6*c₃^2*s₂^2*s₃^6 + 4*c₃^2*s₂^2*s₃^4 - 6*c₃^2*s₃^6 + 4*c₃^2*s₃^4 - 16*s₁^6*s₂^4*s₃^6 - 16*s₁^6*s₂^2*s₃^6 + 16*s₁^6*s₂^2*s₃^4 + 16*s₁^6*s₃^6 - 16*s₁^6*s₃^4 + 24*s₁^4*s₂^4*s₃^6 + 24*s₁^4*s₂^2*s₃^6 - 24*s₁^4*s₂^2*s₃^4 - 24*s₁^4*s₃^6 + 24*s₁^4*s₃^4 + 2*s₁^2*s₂^6*s₃^4 + 16*s₁^2*s₂^4*s₃^6 - 30*s₁^2*s₂^4*s₃^4 + 2*s₁^2*s₂^2*s₃^8 - 32*s₁^2*s₂^2*s₃^6 + 30*s₁^2*s₂^2*s₃^4 - 2*s₁^2*s₃^8 + 16*s₁^2*s₃^6 - 14*s₁^2*s₃^4 - s₂^6*s₃^4 - 12*s₂^4*s₃^6 + 15*s₂^4*s₃^4 - s₂^2*s₃^8 + 12*s₂^2*s₃^6 - 11*s₂^2*s₃^4 + s₃^8 - 4*s₃^6 + 3*s₃^4) * u₂ +
    (-4*c₃^6*s₁^2*s₂^2 + 2*c₃^6*s₁^2 + 2*c₃^6*s₂^2 - c₃^6 + 32*c₃^4*s₁^6*s₂^2 - 16*c₃^4*s₁^6 - 48*c₃^4*s₁^4*s₂^2 + 24*c₃^4*s₁^4 + 32*c₃^4*s₁^2*s₂^6 - 48*c₃^4*s₁^2*s₂^4 + 28*c₃^4*s₁^2*s₂^2*s₃^2 + 44*c₃^4*s₁^2*s₂^2 - 14*c₃^4*s₁^2*s₃^2 - 14*c₃^4*s₁^2 - 16*c₃^4*s₂^6 + 24*c₃^4*s₂^4 - 14*c₃^4*s₂^2*s₃^2 - 14*c₃^4*s₂^2 + 7*c₃^4*s₃^2 + 3*c₃^4 - 28*c₃^2*s₁^2*s₂^2*s₃^4 + 14*c₃^2*s₁^2*s₃^4 + 14*c₃^2*s₂^2*s₃^4 - 7*c₃^2*s₃^4 - 32*s₁^6*s₂^2*s₃^4 + 16*s₁^6*s₃^4 + 48*s₁^4*s₂^2*s₃^4 - 24*s₁^4*s₃^4 - 32*s₁^2*s₂^6*s₃^4 + 48*s₁^2*s₂^4*s₃^4 + 4*s₁^2*s₂^2*s₃^6 - 44*s₁^2*s₂^2*s₃^4 - 2*s₁^2*s₃^6 + 14*s₁^2*s₃^4 + 16*s₂^6*s₃^4 - 24*s₂^4*s₃^4 - 2*s₂^2*s₃^6 + 14*s₂^2*s₃^4 + s₃^6 - 3*s₃^4) * u₃
end Ring

/-- The half-side cosine `κ² − σ²` from a quarter pair. -/
abbrev hc (σ κ : ZT n) : ZT n := κ * κ - σ * σ
/-- `cos a = (κ² − σ²)² − (2σκ)²` from a quarter pair. -/
abbrev fc (σ κ : ZT n) : ZT n := hc σ κ * hc σ κ - (ZT.natLit 2 * σ * κ) * (ZT.natLit 2 * σ * κ)

/-- L'Huilier (10.14), cross-multiplied over integer terms. -/
theorem lhuilier {s₁ c₁ s₂ c₂ s₃ c₃ : ZT n} (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1)) (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      ((ZT.natLit 4 * hc s₁ c₁ * hc s₂ c₂ * hc s₃ c₃ - (ZT.natLit 1 + fc s₁ c₁ + fc s₂ c₂ + fc s₃ c₃)) *
        (cos3 s₁ c₁ s₂ c₂ s₃ c₃ * cos3 (-s₁) c₁ s₂ c₂ s₃ c₃ * cos3 s₁ c₁ (-s₂) c₂ s₃ c₃ * cos3 s₁ c₁ s₂ c₂ (-s₃) c₃))
      ((ZT.natLit 4 * hc s₁ c₁ * hc s₂ c₂ * hc s₃ c₃ + (ZT.natLit 1 + fc s₁ c₁ + fc s₂ c₂ + fc s₃ c₃)) *
        (sin3 s₁ c₁ s₂ c₂ s₃ c₃ * sin3 (-s₁) c₁ s₂ c₂ s₃ c₃ * sin3 s₁ c₁ (-s₂) c₂ s₃ c₃ * sin3 s₁ c₁ s₂ c₂ (-s₃) c₃)) := by
  have e₁ := ZT.toZ_eq u₁; have e₂ := ZT.toZ_eq u₂; have e₃ := ZT.toZ_eq u₃
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one] at e₁ e₂ e₃
  have k := lhuilierR _ _ _ _ _ _ e₁ e₂ e₃
  refine ZT.derive ?_
  simp only [toZ_sin3, toZ_cos3, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]
  simp only [sin3R, cos3R] at k ⊢
  push_cast
  linear_combination k

end LeanProofs.IPRA.Geometry.SphericalArea
