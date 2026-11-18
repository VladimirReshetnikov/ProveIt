import IPRADerivations.Geometry.CevaMenelaus

/-!
# Mollweide's formulas, the law of tangents and the inradius

Packet: `mollweide_circle_ipra`, Sections 3–6: the ring certificates behind the half-angle
treatment of a triangle with sides `a = y + z`, `b = z + x`, `c = x + y` and semiperimeter
`s = x + y + z` (`x = s − a`, …). All statements are division-free equations of integer terms
(`ZT`); the half-angle components `s_A, c_A, …` and the scale `d` are arbitrary terms subject to the
displayed hypotheses, so the certificates hold for any representation respecting ring identities.

* `unit_A`, `unit_B`, `unit_C`: `yz + sx = bc`, … (the unit equations cleared of `bc`);
* `cos_poly`: `b² + c² − a² = 2(sx − yz)`;
* `heron_factor`, `heron_xyz`: `(a+b+c)(−a+b+c)(a−b+c)(a+b−c) = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`,
  and with the Ravi sides it equals `16 s x y z`;
* `complement_cos`, `complement_sin` (Theorem "Algebraic complement formula"): from the four
  product equations and `c ≠ 0`, `c_C = s_A c_B + c_A s_B` and `s_C = c_A c_B − s_A s_B`;
* `mollweide_sum`, `mollweide_diff` (Theorem "Denominator-free Mollweide formulas"):
  `(a + b) s_C = c c_D` and `(a − b) c_C = c s_D` for `s_D = s_A c_B − c_A s_B`,
  `c_D = c_A c_B + s_A s_B`;
* `tangent_cross` (denominator-free law of tangents): `(a − b) c_D c_C = (a + b) s_D s_C`;
* `inradius` (Corollary "Inradius formula"): `r s = K` and `K² = s x y z` give `r² s = x y z`.

The positive square roots, the regular-name constructions and the quotient corollaries are not
formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.Mollweide

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.CevaMenelaus (nz zt_cancel)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Ravi

variable (x y z : ZT n)

/-- `yz + sx = bc`. -/
theorem unit_A : Γ ⊢[PRAAx] ZT.eq (y * z + (x + y + z) * x) ((z + x) * (x + y)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_mul]; ring)

/-- `zx + sy = ca`. -/
theorem unit_B : Γ ⊢[PRAAx] ZT.eq (z * x + (x + y + z) * y) ((x + y) * (y + z)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_mul]; ring)

/-- `xy + sz = ab`. -/
theorem unit_C : Γ ⊢[PRAAx] ZT.eq (x * y + (x + y + z) * z) ((y + z) * (z + x)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_mul]; ring)

/-- `b² + c² − a² = 2(sx − yz)`. -/
theorem cos_poly :
    Γ ⊢[PRAAx] ZT.eq ((z + x) * (z + x) + (x + y) * (x + y) - (y + z) * (y + z))
      (ZT.natLit 2 * ((x + y + z) * x - y * z)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]; push_cast; ring)

/-- With the Ravi sides, the Heron product is `16 s x y z`. -/
theorem heron_xyz :
    Γ ⊢[PRAAx] ZT.eq ((y + z + (z + x) + (x + y)) * (-(y + z) + (z + x) + (x + y)) *
        ((y + z) - (z + x) + (x + y)) * ((y + z) + (z + x) - (x + y)))
      (ZT.natLit 16 * ((x + y + z) * x * y * z)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]; push_cast; ring)

end Ravi

/-- `(a+b+c)(−a+b+c)(a−b+c)(a+b−c) = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`. -/
theorem heron_factor (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c))
      (ZT.natLit 2 * (a * a * (b * b)) + ZT.natLit 2 * (b * b * (c * c)) + ZT.natLit 2 * (c * c * (a * a)) -
        a * a * (a * a) - b * b * (b * b) - c * c * (c * c)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]; push_cast; ring)

/-! ## The complement formula -/

section Half

variable {x y z c sA cA sB cB sC cC : ZT n}

/-- `c_C = s_A c_B + c_A s_B` from `c s_A c_B = y c_C`, `c c_A s_B = x c_C`, `c = x + y`, `c ≠ 0`. -/
theorem complement_cos (hc : Γ ⊢[PRAAx] nz c) (hxy : Γ ⊢[PRAAx] ZT.eq c (x + y))
    (p₁ : Γ ⊢[PRAAx] ZT.eq (c * sA * cB) (y * cC)) (p₂ : Γ ⊢[PRAAx] ZT.eq (c * cA * sB) (x * cC)) :
    Γ ⊢[PRAAx] ZT.eq (sA * cB + cA * sB) cC := by
  have e := ZT.toZ_eq hxy; have e₁ := ZT.toZ_eq p₁; have e₂ := ZT.toZ_eq p₂
  simp only [ZT.toZ_add, ZT.toZ_mul] at e e₁ e₂
  refine zt_cancel hc (ZT.derive ?_)
  simp only [ZT.toZ_add, ZT.toZ_mul]
  linear_combination e₁ + e₂ - ZT.toZ Γ cC * e

/-- `s_C = c_A c_B − s_A s_B` from `c c_A c_B = s s_C`, `c s_A s_B = z s_C`, `c = x + y`,
`s = x + y + z`, `c ≠ 0`. -/
theorem complement_sin {s : ZT n} (hc : Γ ⊢[PRAAx] nz c) (hxy : Γ ⊢[PRAAx] ZT.eq c (x + y))
    (hs : Γ ⊢[PRAAx] ZT.eq s (x + y + z))
    (p₃ : Γ ⊢[PRAAx] ZT.eq (c * cA * cB) (s * sC)) (p₄ : Γ ⊢[PRAAx] ZT.eq (c * sA * sB) (z * sC)) :
    Γ ⊢[PRAAx] ZT.eq (cA * cB - sA * sB) sC := by
  have e := ZT.toZ_eq hxy; have es := ZT.toZ_eq hs; have e₃ := ZT.toZ_eq p₃; have e₄ := ZT.toZ_eq p₄
  simp only [ZT.toZ_add, ZT.toZ_mul] at e es e₃ e₄
  refine zt_cancel hc (ZT.derive ?_)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]
  linear_combination e₃ - e₄ + ZT.toZ Γ sC * es - ZT.toZ Γ sC * e

end Half

/-! ## Mollweide and the law of tangents -/

section Moll

variable {a b c d sA cA sB cB sC cC : ZT n}

/-- `(s_A c_B + c_A s_B)(c_A c_B + s_A s_B) = s_A c_A + s_B c_B` for unit pairs. -/
theorem prod_sum (uA : Γ ⊢[PRAAx] ZT.eq (sA * sA + cA * cA) (ZT.natLit 1))
    (uB : Γ ⊢[PRAAx] ZT.eq (sB * sB + cB * cB) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq ((sA * cB + cA * sB) * (cA * cB + sA * sB)) (sA * cA + sB * cB) := by
  have a₁ := ZT.toZ_eq uA; have b₁ := ZT.toZ_eq uB
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at a₁ b₁
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul]
  push_cast at a₁ b₁
  linear_combination ZT.toZ Γ sA * ZT.toZ Γ cA * b₁ + ZT.toZ Γ sB * ZT.toZ Γ cB * a₁

/-- `(c_A c_B − s_A s_B)(s_A c_B − c_A s_B) = s_A c_A − s_B c_B` for unit pairs. -/
theorem prod_diff (uA : Γ ⊢[PRAAx] ZT.eq (sA * sA + cA * cA) (ZT.natLit 1))
    (uB : Γ ⊢[PRAAx] ZT.eq (sB * sB + cB * cB) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq ((cA * cB - sA * sB) * (sA * cB - cA * sB)) (sA * cA - sB * cB) := by
  have a₁ := ZT.toZ_eq uA; have b₁ := ZT.toZ_eq uB
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at a₁ b₁
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]
  push_cast at a₁ b₁
  linear_combination ZT.toZ Γ sA * ZT.toZ Γ cA * b₁ - ZT.toZ Γ sB * ZT.toZ Γ cB * a₁

/-- Mollweide, sum form: `(a + b) s_C = c c_D`. -/
theorem mollweide_sum (uA : Γ ⊢[PRAAx] ZT.eq (sA * sA + cA * cA) (ZT.natLit 1))
    (uB : Γ ⊢[PRAAx] ZT.eq (sB * sB + cB * cB) (ZT.natLit 1))
    (hC : Γ ⊢[PRAAx] ZT.eq (sA * cB + cA * sB) cC)
    (ha : Γ ⊢[PRAAx] ZT.eq a (ZT.natLit 2 * d * (sA * cA))) (hb : Γ ⊢[PRAAx] ZT.eq b (ZT.natLit 2 * d * (sB * cB)))
    (hc : Γ ⊢[PRAAx] ZT.eq c (ZT.natLit 2 * d * (sC * cC))) :
    Γ ⊢[PRAAx] ZT.eq ((a + b) * sC) (c * (cA * cB + sA * sB)) := by
  have ps := ZT.toZ_eq (prod_sum uA uB)
  have eC := ZT.toZ_eq hC; have ea := ZT.toZ_eq ha; have eb := ZT.toZ_eq hb; have ec := ZT.toZ_eq hc
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at ps eC ea eb ec
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul]
  push_cast at ea eb ec
  linear_combination ZT.toZ Γ sC * ea + ZT.toZ Γ sC * eb - (ZT.toZ Γ cA * ZT.toZ Γ cB + ZT.toZ Γ sA * ZT.toZ Γ sB) * ec -
    2 * ZT.toZ Γ d * ZT.toZ Γ sC * ps +
    2 * ZT.toZ Γ d * ZT.toZ Γ sC * (ZT.toZ Γ cA * ZT.toZ Γ cB + ZT.toZ Γ sA * ZT.toZ Γ sB) * eC

/-- Mollweide, difference form: `(a − b) c_C = c s_D`. -/
theorem mollweide_diff (uA : Γ ⊢[PRAAx] ZT.eq (sA * sA + cA * cA) (ZT.natLit 1))
    (uB : Γ ⊢[PRAAx] ZT.eq (sB * sB + cB * cB) (ZT.natLit 1))
    (hS : Γ ⊢[PRAAx] ZT.eq (cA * cB - sA * sB) sC)
    (ha : Γ ⊢[PRAAx] ZT.eq a (ZT.natLit 2 * d * (sA * cA))) (hb : Γ ⊢[PRAAx] ZT.eq b (ZT.natLit 2 * d * (sB * cB)))
    (hc : Γ ⊢[PRAAx] ZT.eq c (ZT.natLit 2 * d * (sC * cC))) :
    Γ ⊢[PRAAx] ZT.eq ((a - b) * cC) (c * (sA * cB - cA * sB)) := by
  have pd := ZT.toZ_eq (prod_diff uA uB)
  have eS := ZT.toZ_eq hS; have ea := ZT.toZ_eq ha; have eb := ZT.toZ_eq hb; have ec := ZT.toZ_eq hc
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at pd eS ea eb ec
  refine ZT.derive ?_
  simp only [ZT.toZ_sub, ZT.toZ_mul]
  push_cast at ea eb ec
  linear_combination ZT.toZ Γ cC * ea - ZT.toZ Γ cC * eb - (ZT.toZ Γ sA * ZT.toZ Γ cB - ZT.toZ Γ cA * ZT.toZ Γ sB) * ec -
    2 * ZT.toZ Γ d * ZT.toZ Γ cC * pd +
    2 * ZT.toZ Γ d * ZT.toZ Γ cC * (ZT.toZ Γ sA * ZT.toZ Γ cB - ZT.toZ Γ cA * ZT.toZ Γ sB) * eS

/-- The denominator-free law of tangents: `(a − b) c_D c_C = (a + b) s_D s_C`. -/
theorem tangent_cross {sD cD : ZT n} (m₁ : Γ ⊢[PRAAx] ZT.eq ((a + b) * sC) (c * cD))
    (m₂ : Γ ⊢[PRAAx] ZT.eq ((a - b) * cC) (c * sD)) :
    Γ ⊢[PRAAx] ZT.eq ((a - b) * cD * cC) ((a + b) * sD * sC) := by
  have e₁ := ZT.toZ_eq m₁; have e₂ := ZT.toZ_eq m₂
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul] at e₁ e₂
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]
  linear_combination ZT.toZ Γ cD * e₂ - ZT.toZ Γ sD * e₁

end Moll

/-- The inradius formula: `r s = K`, `K² = s x y z` and `s ≠ 0` give `r² s = x y z`. -/
theorem inradius {r s K x y z : ZT n} (hs : Γ ⊢[PRAAx] nz s) (h₁ : Γ ⊢[PRAAx] ZT.eq (r * s) K)
    (h₂ : Γ ⊢[PRAAx] ZT.eq (K * K) (s * x * y * z)) : Γ ⊢[PRAAx] ZT.eq (r * r * s) (x * y * z) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  simp only [ZT.toZ_mul] at e₁ e₂
  refine zt_cancel hs (ZT.derive ?_)
  simp only [ZT.toZ_mul]
  linear_combination (ZT.toZ Γ r * ZT.toZ Γ s + ZT.toZ Γ K) * e₁ + e₂

/-! ## The incenter -/

/-- `lem:incenter-distance`, cleared: if `(a + b + c) I = a A + b B + c C` coordinatewise, then
`(a + b + c) det(C − B, I − B) = a det(C − B, A − B)`, i.e. the signed distance of `I` from the side `BC`
is `2aK / ((a + b + c) a) = K/s = r`; the other two sides are the cyclic instances. -/
theorem incenter_distance {a b c Ax Ay Bx By Cx Cy Ix Iy : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq ((a + b + c) * Ix) (a * Ax + b * Bx + c * Cx))
    (hy : Γ ⊢[PRAAx] ZT.eq ((a + b + c) * Iy) (a * Ay + b * By + c * Cy)) :
    Γ ⊢[PRAAx] ZT.eq ((a + b + c) * ((Cx - Bx) * (Iy - By) - (Cy - By) * (Ix - Bx)))
      (a * ((Cx - Bx) * (Ay - By) - (Cy - By) * (Ax - Bx))) := by
  have e₁ := ZT.toZ_eq hx; have e₂ := ZT.toZ_eq hy
  simp only [ZT.toZ_mul, ZT.toZ_add] at e₁ e₂
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub]
  linear_combination (ZT.toZ Γ Cx - ZT.toZ Γ Bx) * e₂ - (ZT.toZ Γ Cy - ZT.toZ Γ By) * e₁

end LeanProofs.IPRA.Geometry.Mollweide
