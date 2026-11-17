import IPRADerivations.Geometry.CevaMenelaus

/-!
# The Delambre–Gauss analogies, squared

Packet: `spherical_trigonometry_ipra_2026-11-15`, `sections/07_analogies.tex`, Theorem
`thm:delambre`. Squaring (7.1)–(7.4) and replacing every half-square by `(1 ± cos)/2` gives the
four polynomial identities proved here, from

* the angle cosine law `cos C = −cos A cos B + sin A sin B cos c`,
* the side cosine law `cos c = cos a cos b + sin a sin b cos C`,
* the doubled sine law (7.6) `sin A sin B sin² c = sin a sin b sin² C`,
* the unit relations `sin² c + cos² c = 1`, `sin² C + cos² C = 1`.

* `delambre1` (7.5), the square of (7.1): `(1 − cos(A + B))(1 + cos c) = (1 + cos(a − b))(1 + cos C)`;
* `delambre2`, the square of (7.2): `(1 − cos(A − B))(1 − cos c) = (1 − cos(a − b))(1 + cos C)`;
* `delambre3`, the square of (7.3): `(1 + cos(A + B))(1 + cos c) = (1 + cos(a + b))(1 − cos C)`;
* `delambre4`, the square of (7.4): `(1 + cos(A − B))(1 − cos c) = (1 − cos(a + b))(1 − cos C)`,

with `cos(A ± B) = cos A cos B ∓ sin A sin B` and likewise for the sides. Each is proved over a
commutative ring and read as an equation of integer terms. The nonnegative square roots and the
quotient forms (7.7)–(7.17) are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.SphericalDelambre

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Ring

variable {R : Type*} [CommRing R] {cA sA cB sB cC sC ca sa cb sb cc sc : R}

theorem d1R (gC : cC = -(cA * cB) + sA * sB * cc) (gc : cc = ca * cb + sa * sb * cC)
    (gs : sA * sB * (sc * sc) = sa * sb * (sC * sC)) (uc : sc * sc + cc * cc = 1) (uC : sC * sC + cC * cC = 1) :
    (1 - (cA * cB - sA * sB)) * (1 + cc) = (1 + (ca * cb + sa * sb)) * (1 + cC) := by
  linear_combination gs - sA * sB * uc + sa * sb * uC - (1 + cc) * gC + (1 + cC) * gc

theorem d2R (gC : cC = -(cA * cB) + sA * sB * cc) (gc : cc = ca * cb + sa * sb * cC)
    (gs : sA * sB * (sc * sc) = sa * sb * (sC * sC)) (uc : sc * sc + cc * cc = 1) (uC : sC * sC + cC * cC = 1) :
    (1 - (cA * cB + sA * sB)) * (1 - cc) = (1 - (ca * cb + sa * sb)) * (1 + cC) := by
  linear_combination -gs + sA * sB * uc - sa * sb * uC - (1 - cc) * gC - (1 + cC) * gc

theorem d3R (gC : cC = -(cA * cB) + sA * sB * cc) (gc : cc = ca * cb + sa * sb * cC)
    (gs : sA * sB * (sc * sc) = sa * sb * (sC * sC)) (uc : sc * sc + cc * cc = 1) (uC : sC * sC + cC * cC = 1) :
    (1 + (cA * cB - sA * sB)) * (1 + cc) = (1 + (ca * cb - sa * sb)) * (1 - cC) := by
  linear_combination -gs + sA * sB * uc - sa * sb * uC + (1 + cc) * gC + (1 - cC) * gc

theorem d4R (gC : cC = -(cA * cB) + sA * sB * cc) (gc : cc = ca * cb + sa * sb * cC)
    (gs : sA * sB * (sc * sc) = sa * sb * (sC * sC)) (uc : sc * sc + cc * cc = 1) (uC : sC * sC + cC * cC = 1) :
    (1 + (cA * cB + sA * sB)) * (1 - cc) = (1 - (ca * cb - sa * sb)) * (1 - cC) := by
  linear_combination gs - sA * sB * uc + sa * sb * uC + (1 - cc) * gC - (1 - cC) * gc

end Ring

section Terms

variable {cA sA cB sB cC sC ca sa cb sb cc sc : ZT n}

/-- The hypotheses: two cosine laws, the doubled sine law and two unit relations. -/
structure Laws (cA sA cB sB cC sC ca sa cb sb cc sc : ZT n) (Γ : List (Fm PTm n)) : Prop where
  gC : Nonempty (Γ ⊢[PRAAx] ZT.eq cC (-(cA * cB) + sA * sB * cc))
  gc : Nonempty (Γ ⊢[PRAAx] ZT.eq cc (ca * cb + sa * sb * cC))
  gs : Nonempty (Γ ⊢[PRAAx] ZT.eq (sA * sB * (sc * sc)) (sa * sb * (sC * sC)))
  uc : Nonempty (Γ ⊢[PRAAx] ZT.eq (sc * sc + cc * cc) (ZT.natLit 1))
  uC : Nonempty (Γ ⊢[PRAAx] ZT.eq (sC * sC + cC * cC) (ZT.natLit 1))

theorem laws_toZ (h : Laws cA sA cB sB cC sC ca sa cb sb cc sc Γ) :
    ZT.toZ Γ cC = -(ZT.toZ Γ cA * ZT.toZ Γ cB) + ZT.toZ Γ sA * ZT.toZ Γ sB * ZT.toZ Γ cc ∧
    ZT.toZ Γ cc = ZT.toZ Γ ca * ZT.toZ Γ cb + ZT.toZ Γ sa * ZT.toZ Γ sb * ZT.toZ Γ cC ∧
    ZT.toZ Γ sA * ZT.toZ Γ sB * (ZT.toZ Γ sc * ZT.toZ Γ sc) = ZT.toZ Γ sa * ZT.toZ Γ sb * (ZT.toZ Γ sC * ZT.toZ Γ sC) ∧
    ZT.toZ Γ sc * ZT.toZ Γ sc + ZT.toZ Γ cc * ZT.toZ Γ cc = 1 ∧
    ZT.toZ Γ sC * ZT.toZ Γ sC + ZT.toZ Γ cC * ZT.toZ Γ cC = 1 := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩, ⟨d⟩, ⟨e⟩⟩ := h
  have a' := ZT.toZ_eq a; have b' := ZT.toZ_eq b; have c' := ZT.toZ_eq c
  have d' := ZT.toZ_eq d; have e' := ZT.toZ_eq e
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_one] at a' b' c' d' e'
  exact ⟨a', b', c', d', e'⟩

/-- (7.5), the square of (7.1). -/
theorem delambre1 (h : Laws cA sA cB sB cC sC ca sa cb sb cc sc Γ) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 - (cA * cB - sA * sB)) * (ZT.natLit 1 + cc))
      ((ZT.natLit 1 + (ca * cb + sa * sb)) * (ZT.natLit 1 + cC)) := by
  obtain ⟨a, b, c, d, e⟩ := laws_toZ h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
  exact d1R a b c d e

/-- The square of (7.2). -/
theorem delambre2 (h : Laws cA sA cB sB cC sC ca sa cb sb cc sc Γ) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 - (cA * cB + sA * sB)) * (ZT.natLit 1 - cc))
      ((ZT.natLit 1 - (ca * cb + sa * sb)) * (ZT.natLit 1 + cC)) := by
  obtain ⟨a, b, c, d, e⟩ := laws_toZ h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
  exact d2R a b c d e

/-- The square of (7.3). -/
theorem delambre3 (h : Laws cA sA cB sB cC sC ca sa cb sb cc sc Γ) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 + (cA * cB - sA * sB)) * (ZT.natLit 1 + cc))
      ((ZT.natLit 1 + (ca * cb - sa * sb)) * (ZT.natLit 1 - cC)) := by
  obtain ⟨a, b, c, d, e⟩ := laws_toZ h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
  exact d3R a b c d e

/-- The square of (7.4). -/
theorem delambre4 (h : Laws cA sA cB sB cC sC ca sa cb sb cc sc Γ) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 + (cA * cB + sA * sB)) * (ZT.natLit 1 - cc))
      ((ZT.natLit 1 - (ca * cb - sa * sb)) * (ZT.natLit 1 - cC)) := by
  obtain ⟨a, b, c, d, e⟩ := laws_toZ h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
  exact d4R a b c d e

end Terms

end LeanProofs.IPRA.Geometry.SphericalDelambre
