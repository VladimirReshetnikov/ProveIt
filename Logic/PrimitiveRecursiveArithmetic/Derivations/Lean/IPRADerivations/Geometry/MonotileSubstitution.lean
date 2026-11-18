import IPRADerivations.Core.PolynomialImplications

/-!
# The substitution matrix of the hat metatiles (`aperiodic_monotile_ipra_2026-11-16`)

Packet: `geometry/aperiodic_monotile_ipra_2026-11-16`. `Geometry/TriangularNorm` derives the
descent `lem:qparity`, `lem:nosqrt2`. This module derives the exact facts about the
substitution matrix of the four metatiles `H, T, P, F`,

  `M = [[3, 1, 3, 3], [1, 0, 0, 0], [2, 0, 1, 2], [2, 0, 1, 3]]`,

whose row `i` lists how many children of each type the supertile of type `i` contains
(`10, 1, 5, 6` children in total).

* `char_poly`: `det (x I − M) = x⁴ − 7 x³ + 7 x − 1`, the determinant being the cofactor
  expansion `det4` along the first row;
* `char_poly_factor`: `x⁴ − 7 x³ + 7 x − 1 = (x − 1)(x + 1)(x² − 7 x + 1)`, the displayed
  factorization `χ_M(x) = (x − 1)(x + 1)(x² − 7x + 1)`.

The area lemma `lem:area`, the substitution step, the covering radius, the torus obstruction and the geometric
aperiodicity theorem are not derived.
-/

namespace LeanProofs.IPRA.Geometry.MonotileSubstitution

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-- A row of a `4 × 4` matrix. -/
structure Row4 (k : ℕ) where
  a : ZExp k
  b : ZExp k
  c : ZExp k
  d : ZExp k

/-- The `4 × 4` determinant, by cofactor expansion along the first row. -/
def det4 {k : ℕ} (r₁ r₂ r₃ r₄ : Row4 k) : ZExp k :=
  r₁.a * det3 ⟨r₂.b, r₂.c, r₂.d⟩ ⟨r₃.b, r₃.c, r₃.d⟩ ⟨r₄.b, r₄.c, r₄.d⟩ -
    r₁.b * det3 ⟨r₂.a, r₂.c, r₂.d⟩ ⟨r₃.a, r₃.c, r₃.d⟩ ⟨r₄.a, r₄.c, r₄.d⟩ +
    r₁.c * det3 ⟨r₂.a, r₂.b, r₂.d⟩ ⟨r₃.a, r₃.b, r₃.d⟩ ⟨r₄.a, r₄.b, r₄.d⟩ -
    r₁.d * det3 ⟨r₂.a, r₂.b, r₂.c⟩ ⟨r₃.a, r₃.b, r₃.c⟩ ⟨r₄.a, r₄.b, r₄.c⟩

section CharPoly

local notation "x" => (ZExp.var 0 : ZExp 1)

/-- `det (x I − M) = x⁴ − 7 x³ + 7 x − 1`. -/
theorem char_poly :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp [] (det4 (Row4.mk (x - 3) (0 - 1) (0 - 3) (0 - 3)) (Row4.mk (0 - 1) x 0 0)
          (Row4.mk (0 - 2) 0 (x - 1) (0 - 2)) (Row4.mk (0 - 2) 0 (0 - 1) (x - 3)),
        x ^ 4 - 7 * x ^ 3 + 7 * x - 1)) :=
  derive_imp _ _ (by ipra_poly R ρ h [det4]; ring)

/-- `x⁴ − 7 x³ + 7 x − 1 = (x − 1)(x + 1)(x² − 7 x + 1)`. -/
theorem char_poly_factor :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp [] (x ^ 4 - 7 * x ^ 3 + 7 * x - 1, (x - 1) * (x + 1) * (x ^ 2 - 7 * x + 1))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end CharPoly

end LeanProofs.IPRA.Geometry.MonotileSubstitution
