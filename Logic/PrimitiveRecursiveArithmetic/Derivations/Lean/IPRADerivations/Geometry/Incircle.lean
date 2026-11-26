import IPRADerivations.Geometry.TriangleCentres

/-!
# Angle bisectors, the incircle, the excircles and Euler's `OI` identity

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/triangles.tex`, Theorems `tri:bisector`,
`tri:incenter`, `tri:excenters` and `tri:euler-inequality`. Points have two integer-term coordinates, with `dot`,
`det`, `nsq` of `Geometry/TriangleCentres`; the side lengths `a, b, c` are integer terms, with the equations
`a² = |B − C|²`, `b² = |C − A|²`, `c² = |A − B|²` as hypotheses where they are used. With `P = a + b + c`,
`D = [B − A, C − A]` and the scaled incentre `P I = a A + b B + c C`, as iPRA derivations:

* `bisector_det`, `bisector_dot`: for `u = B − A`, `v = C − A` and the direction `w = b u + c v` of
  `T − A = (b (B − A) + c (C − A))/(b + c)`: `b [u, w] = c [w, v]` and `b (u · w) = c (w · v)`, the equal sines and
  cosines "`[e, d] = [d, f]`", "`e · d = f · d`" of the unit directions, cleared;
* `incentre_BC`, `incentre_CA`, `incentre_AB`: "`[C − B, I − B] = a D/P`, `[A − C, I − C] = b D/P`,
  `[B − A, I − A] = c D/P`", times `P`: the common distance `r = D/P`;
* `incircle_foot`: the foot parameter "`t = (I − B) · (C − B)/a² = (a + c − b)/(2a)`", as
  `2 (P I − P B) · (C − B) = a (a + c − b) P`;
* `excentre_BC`, `excentre_CA`, `excentre_AB`: for `P_A I_A = −a A + b B + c C`, "signed doubled subareas
  `−a D/P_A`, `b D/P_A`, `c D/P_A`";
* `euler_identity`: "`|a x + b y + c z|² = P (a |x|² + b |y|² + c |z|²) − ab |x − y|² − bc |y − z|² −
  ca |z − x|²`";
* `euler_OI`: with the circumcentre as origin (`|x|² = |y|² = |z|² = ρ`), `|P I|² = P² ρ − a b c P`, that is
  "`|I|² = R² − abc/P`" `= R (R − 2r)`;
* `euler_inequality`: `a b c P ≤ P² ρ`, that is "`R ≥ 2r`".

Not derived: the uniqueness statements, the equality case of Euler's inequality, and Viviani's theorem beyond the
subarea identity `Geometry/AffinePlane.subarea_sum`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.Incircle

open_ipra
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

attribute [local ipra_defs] dot det nsq

/-! ## The internal bisector -/

/-- `b [u, w] = c [w, v]` for `w = b u + c v`. -/
theorem bisector_det (u₁ u₂ v₁ v₂ b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (b * det u₁ u₂ (b * u₁ + c * v₁) (b * u₂ + c * v₂))
      (c * det (b * u₁ + c * v₁) (b * u₂ + c * v₂) v₁ v₂) := by
  ipra_lc

/-- `b (u · w) = c (w · v)` for `w = b u + c v`, when `c² = |u|²` and `b² = |v|²`. -/
theorem bisector_dot {u₁ u₂ v₁ v₂ b c : ZT n} (hc : Γ ⊢[PRAAx] ZT.eq (c * c) (nsq u₁ u₂))
    (hb : Γ ⊢[PRAAx] ZT.eq (b * b) (nsq v₁ v₂)) :
    Γ ⊢[PRAAx] ZT.eq (b * dot u₁ u₂ (b * u₁ + c * v₁) (b * u₂ + c * v₂))
      (c * dot (b * u₁ + c * v₁) (b * u₂ + c * v₂) v₁ v₂) := by
  ipra_lc (-(ZT.toZ Γ b * ZT.toZ Γ b)) * ZT.toZ_eq hc + (ZT.toZ Γ c * ZT.toZ Γ c) * ZT.toZ_eq hb

/-! ## The incentre -/

/-- `[C − B, P I − P B] = a D`. -/
theorem incentre_BC (a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (c₁ - b₁) (c₂ - b₂) (a * a₁ + b * b₁ + c * c₁ - (a + b + c) * b₁)
        (a * a₂ + b * b₂ + c * c₂ - (a + b + c) * b₂))
      (a * det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- `[A − C, P I − P C] = b D`. -/
theorem incentre_CA (a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (a₁ - c₁) (a₂ - c₂) (a * a₁ + b * b₁ + c * c₁ - (a + b + c) * c₁)
        (a * a₂ + b * b₂ + c * c₂ - (a + b + c) * c₂))
      (b * det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- `[B − A, P I − P A] = c D`. -/
theorem incentre_AB (a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (b₁ - a₁) (b₂ - a₂) (a * a₁ + b * b₁ + c * c₁ - (a + b + c) * a₁)
        (a * a₂ + b * b₂ + c * c₂ - (a + b + c) * a₂))
      (c * det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- The foot of the incentre on `BC`: `2 (P I − P B) · (C − B) = a (a + c − b) P`. -/
theorem incircle_foot {a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (a * a) (nsq (c₁ - b₁) (c₂ - b₂)))
    (hb : Γ ⊢[PRAAx] ZT.eq (b * b) (nsq (c₁ - a₁) (c₂ - a₂)))
    (hc : Γ ⊢[PRAAx] ZT.eq (c * c) (nsq (a₁ - b₁) (a₂ - b₂))) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * dot (a * a₁ + b * b₁ + c * c₁ - (a + b + c) * b₁)
        (a * a₂ + b * b₂ + c * c₂ - (a + b + c) * b₂) (c₁ - b₁) (c₂ - b₂))
      (a * (a + c - b) * (a + b + c)) := by
  ipra_lc (-(ZT.toZ Γ a + 2 * ZT.toZ Γ c)) * ZT.toZ_eq ha - ZT.toZ Γ a * ZT.toZ_eq hc + ZT.toZ Γ a * ZT.toZ_eq hb

/-! ## The excentre opposite `A` -/

/-- `[C − B, P_A I_A − P_A B] = −a D`. -/
theorem excentre_BC (a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (c₁ - b₁) (c₂ - b₂) (-a * a₁ + b * b₁ + c * c₁ - (-a + b + c) * b₁)
        (-a * a₂ + b * b₂ + c * c₂ - (-a + b + c) * b₂))
      (-a * det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- `[A − C, P_A I_A − P_A C] = b D`. -/
theorem excentre_CA (a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (a₁ - c₁) (a₂ - c₂) (-a * a₁ + b * b₁ + c * c₁ - (-a + b + c) * c₁)
        (-a * a₂ + b * b₂ + c * c₂ - (-a + b + c) * c₂))
      (b * det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- `[B − A, P_A I_A − P_A A] = c D`. -/
theorem excentre_AB (a₁ a₂ b₁ b₂ c₁ c₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (b₁ - a₁) (b₂ - a₂) (-a * a₁ + b * b₁ + c * c₁ - (-a + b + c) * a₁)
        (-a * a₂ + b * b₂ + c * c₂ - (-a + b + c) * a₂))
      (c * det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-! ## Euler's identity -/

/-- `|a x + b y + c z|² = P (a |x|² + b |y|² + c |z|²) − ab |x − y|² − bc |y − z|² − ca |z − x|²`. -/
theorem euler_identity (x₁ x₂ y₁ y₂ z₁ z₂ a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (a * x₁ + b * y₁ + c * z₁) (a * x₂ + b * y₂ + c * z₂))
      ((a + b + c) * (a * nsq x₁ x₂ + b * nsq y₁ y₂ + c * nsq z₁ z₂) -
        a * b * nsq (x₁ - y₁) (x₂ - y₂) - b * c * nsq (y₁ - z₁) (y₂ - z₂) -
        c * a * nsq (z₁ - x₁) (z₂ - x₂)) := by
  ipra_lc

/-- With the circumcentre as origin: `|P I|² = P² ρ − a b c P`. -/
theorem euler_OI {x₁ x₂ y₁ y₂ z₁ z₂ a b c ρ : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq (nsq x₁ x₂) ρ) (hy : Γ ⊢[PRAAx] ZT.eq (nsq y₁ y₂) ρ)
    (hz : Γ ⊢[PRAAx] ZT.eq (nsq z₁ z₂) ρ)
    (ha : Γ ⊢[PRAAx] ZT.eq (a * a) (nsq (y₁ - z₁) (y₂ - z₂)))
    (hb : Γ ⊢[PRAAx] ZT.eq (b * b) (nsq (z₁ - x₁) (z₂ - x₂)))
    (hc : Γ ⊢[PRAAx] ZT.eq (c * c) (nsq (x₁ - y₁) (x₂ - y₂))) :
    Γ ⊢[PRAAx] ZT.eq (nsq (a * x₁ + b * y₁ + c * z₁) (a * x₂ + b * y₂ + c * z₂))
      ((a + b + c) * (a + b + c) * ρ - a * b * c * (a + b + c)) := by
  ipra_lc ((ZT.toZ Γ a + ZT.toZ Γ b + ZT.toZ Γ c) * ZT.toZ Γ a) * ZT.toZ_eq hx +
    ((ZT.toZ Γ a + ZT.toZ Γ b + ZT.toZ Γ c) * ZT.toZ Γ b) * ZT.toZ_eq hy +
    ((ZT.toZ Γ a + ZT.toZ Γ b + ZT.toZ Γ c) * ZT.toZ Γ c) * ZT.toZ_eq hz + (ZT.toZ Γ b * ZT.toZ Γ c) * ZT.toZ_eq ha +
    (ZT.toZ Γ c * ZT.toZ Γ a) * ZT.toZ_eq hb + (ZT.toZ Γ a * ZT.toZ Γ b) * ZT.toZ_eq hc

/-- Euler's inequality `R ≥ 2r`, as `a b c P ≤ P² ρ`. -/
theorem euler_inequality {x₁ x₂ y₁ y₂ z₁ z₂ a b c ρ : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq (nsq x₁ x₂) ρ) (hy : Γ ⊢[PRAAx] ZT.eq (nsq y₁ y₂) ρ)
    (hz : Γ ⊢[PRAAx] ZT.eq (nsq z₁ z₂) ρ)
    (ha : Γ ⊢[PRAAx] ZT.eq (a * a) (nsq (y₁ - z₁) (y₂ - z₂)))
    (hb : Γ ⊢[PRAAx] ZT.eq (b * b) (nsq (z₁ - x₁) (z₂ - x₂)))
    (hc : Γ ⊢[PRAAx] ZT.eq (c * c) (nsq (x₁ - y₁) (x₂ - y₂))) :
    Γ ⊢[PRAAx] zle (a * b * c * (a + b + c)) ((a + b + c) * (a + b + c) * ρ) := by
  ipra_zle (ZT.toZ Γ (a * x₁ + b * y₁ + c * z₁) ^ 2 + ZT.toZ Γ (a * x₂ + b * y₂ + c * z₂) ^ 2) with
    -ZT.toZ_eq (euler_OI hx hy hz ha hb hc)

end LeanProofs.IPRA.Geometry.Incircle
