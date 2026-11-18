import IPRADerivations.Core.PolynomialImplications

/-!
# The algebraic certificates of Morley's theorem (`morley_ipra_constructive`)

Packet: `geometry/morley_ipra_constructive` (`morley_ipra.tex`, Section 3 and the proposition
"Checker correctness"). `Geometry/Morley` derives the trisector identity `lem:triple`. This
module derives the other exact identities that the certificate checker of the packet uses,
as implications between integer polynomial equations (`Core/PolynomialImplications`). Angles
occur only through unit pairs `(c, s)`, `c² + s² = 1`, multiplied as complex numbers:
`(c, s)(d, t) = (c d − s t, c t + s d)`.

* `bracket_identity` (3.6): with `U_x = c_x² + s_x² − 1`, `U_y = c_y² + s_y² − 1`,
  `C = c_x c_y − s_x s_y`, `S = s_x c_y + c_x s_y`,
  `s_x² + s_y² − 2 s_x s_y c_a − s_a² = −s_x² U_y − s_y² U_x − 2 s_x s_y (C + c_a) + (S − s_a)(S + s_a)`;
* `bracket_certificate`: if `(c_x, s_x)`, `(c_y, s_y)` are unit pairs whose product is
  `(−c_a, s_a)`, then `k² (s_x² + s_y² − 2 s_x s_y c_a) = (k s_a)²`: the cosine-law bracket of
  a Morley side is a square;
* `shift_imag` (3.2): for `2 u_c = 1`, `2 u_s = ρ`: `2 Im((c, s) u) = s + ρ c`;
* `shift_imag_sq`: `ρ² = 3` gives `2 c ρ + s (1 − ρ²) = 2 (ρ c − s)`, the cleared form of
  `2 Im((c, s) u²) = ρ c − s`;
* `cube_root_re`, `cube_root_im`: `ρ² = 3` gives `1 − 3 ρ² = −8` and `3 ρ − ρ³ = 0`, that is
  `(1 + i ρ)³ = −8`, or `u³ = −1`;
* `sixty_degrees`: `2 u_c = 1` and `u_c² + u_s² = 1` give `(2 u_s)² = 3`;
* `angle_sum_re`, `angle_sum_im` (3.4): for a unit pair `a` and pairs `b`, `g`, `u` with
  `a b g = u` and `u³ = (−1, 0)`: `(b u)(g u) = (−a_c, a_s)`. This is the passage from
  `α + β + γ = 60°` to `(β + 60°) + (γ + 60°) = 180° − α`;
* `sine_law_det` (3.7): `X + t u = Y + r v` gives `t det(u, v) = det(Y − X, v)`;
* `cosine_expansion` (3.8): `|t u − r v|² = t² u·u + r² v·v − 2 t r u·v`.

The assembly of these identities into the equality of the three squared sides needs the
cancellation of the nonzero quantities `Im(g u²)`, `Im(b u²)` that the certificate witnesses by
explicit inverses, and the coding layer of the checker (`thm:ipra-main`); neither is derived
here.
-/

namespace LeanProofs.IPRA.Geometry.MorleyCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The bracket of a side: `s_x, s_y, c_x, c_y, c_a, s_a, k` -/

section Bracket

local notation "sx" => (ZExp.var 0 : ZExp 7)
local notation "sy" => (ZExp.var 1 : ZExp 7)
local notation "cx" => (ZExp.var 2 : ZExp 7)
local notation "cy" => (ZExp.var 3 : ZExp 7)
local notation "ca" => (ZExp.var 4 : ZExp 7)
local notation "sa" => (ZExp.var 5 : ZExp 7)
local notation "kk" => (ZExp.var 6 : ZExp 7)

theorem bracket_identity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [] (sx ^ 2 + sy ^ 2 - 2 * sx * sy * ca - sa ^ 2,
        0 - sx ^ 2 * (cy ^ 2 + sy ^ 2 - 1) - sy ^ 2 * (cx ^ 2 + sx ^ 2 - 1) -
          2 * sx * sy * (cx * cy - sx * sy + ca) +
          (sx * cy + cx * sy - sa) * (sx * cy + cx * sy + sa))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem bracket_certificate :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(cx ^ 2 + sx ^ 2, 1), (cy ^ 2 + sy ^ 2, 1), (cx * cy - sx * sy, 0 - ca),
          (sx * cy + cx * sy, sa)]
        (kk ^ 2 * (sx ^ 2 + sy ^ 2 - 2 * sx * sy * ca), (kk * sa) ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    linear_combination (-(ρ 6 ^ 2 * ρ 1 ^ 2)) * h₁ + (-(ρ 6 ^ 2 * ρ 0 ^ 2)) * h₂ +
      (-2 * ρ 6 ^ 2 * ρ 0 * ρ 1) * h₃ + (ρ 6 ^ 2 * (ρ 0 * ρ 3 + ρ 2 * ρ 1 + ρ 5)) * h₄)

end Bracket

/-! ## The sixty-degree pair: `c, s, ρ, u_c, u_s` -/

section Sixty

local notation "c" => (ZExp.var 0 : ZExp 5)
local notation "s" => (ZExp.var 1 : ZExp 5)
local notation "rho" => (ZExp.var 2 : ZExp 5)
local notation "uc" => (ZExp.var 3 : ZExp 5)
local notation "us" => (ZExp.var 4 : ZExp 5)

theorem shift_imag :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(2 * uc, 1), (2 * us, rho)] (2 * (c * us + s * uc), s + rho * c)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 1 * h₁ + ρ 0 * h₂)

theorem shift_imag_sq :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(rho ^ 2, 3)] (2 * c * rho + s * (1 - rho ^ 2), 2 * (rho * c - s))) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-ρ 1) * h)

theorem cube_root_re :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [(rho ^ 2, 3)] (1 - 3 * rho ^ 2, 0 - 8)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-3 : R) * h)

theorem cube_root_im :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [(rho ^ 2, 3)] (3 * rho - rho ^ 3, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-ρ 2) * h)

theorem sixty_degrees :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(2 * uc, 1), (uc ^ 2 + us ^ 2, 1)] ((2 * us) ^ 2, 3)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (-(2 * ρ 3 + 1)) * h₁ + 4 * h₂)

end Sixty

/-! ## The angle sum: unit pairs `a, b, g, u` -/

section AngleSum

local notation "ac" => (ZExp.var 0 : ZExp 8)
local notation "as" => (ZExp.var 1 : ZExp 8)
local notation "bc" => (ZExp.var 2 : ZExp 8)
local notation "bs" => (ZExp.var 3 : ZExp 8)
local notation "gc" => (ZExp.var 4 : ZExp 8)
local notation "gs" => (ZExp.var 5 : ZExp 8)
local notation "uc" => (ZExp.var 6 : ZExp 8)
local notation "us" => (ZExp.var 7 : ZExp 8)

/-- The real part of the product of two pairs. -/
def re {k : ℕ} (x y z w : ZExp k) : ZExp k := x * z - y * w
/-- The imaginary part of the product of two pairs. -/
def im {k : ℕ} (x y z w : ZExp k) : ZExp k := x * w + y * z

/-- The hypotheses: `|a| = 1`, `a b g = u` and `u³ = −1`. -/
def angleHyps : List (ZExp 8 × ZExp 8) :=
  [(ac ^ 2 + as ^ 2, 1),
   (re (re ac as bc bs) (im ac as bc bs) gc gs, uc),
   (im (re ac as bc bs) (im ac as bc bs) gc gs, us),
   (re (re uc us uc us) (im uc us uc us) uc us, 0 - 1),
   (im (re uc us uc us) (im uc us uc us) uc us, 0)]

theorem angle_sum_re :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp angleHyps (re (re bc bs uc us) (im bc bs uc us) (re gc gs uc us) (im gc gs uc us),
        0 - ac)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [angleHyps, re, im]
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    linear_combination
      (ρ 0 * (ρ 6 ^ 2 - ρ 7 ^ 2) + ρ 1 * (2 * ρ 6 * ρ 7)) * h₂ -
      (ρ 0 * (2 * ρ 6 * ρ 7) - ρ 1 * (ρ 6 ^ 2 - ρ 7 ^ 2)) * h₃ + ρ 0 * h₄ + ρ 1 * h₅ -
      ((ρ 2 * ρ 4 - ρ 3 * ρ 5) * (ρ 6 ^ 2 - ρ 7 ^ 2) -
        (ρ 2 * ρ 5 + ρ 3 * ρ 4) * (2 * ρ 6 * ρ 7)) * h₁)

theorem angle_sum_im :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp angleHyps (im (re bc bs uc us) (im bc bs uc us) (re gc gs uc us) (im gc gs uc us),
        as)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [angleHyps, re, im]
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    linear_combination
      (ρ 0 * (ρ 6 ^ 2 - ρ 7 ^ 2) + ρ 1 * (2 * ρ 6 * ρ 7)) * h₃ +
      (ρ 0 * (2 * ρ 6 * ρ 7) - ρ 1 * (ρ 6 ^ 2 - ρ 7 ^ 2)) * h₂ + ρ 0 * h₅ - ρ 1 * h₄ -
      ((ρ 2 * ρ 4 - ρ 3 * ρ 5) * (2 * ρ 6 * ρ 7) +
        (ρ 2 * ρ 5 + ρ 3 * ρ 4) * (ρ 6 ^ 2 - ρ 7 ^ 2)) * h₁)

end AngleSum

/-! ## The determinant sine law and the cosine expansion: `X, Y, u, v` in the plane, `t, r` -/

section Lines

local notation "X" => (Vec2.mk (ZExp.var 0) (ZExp.var 1) : Vec2 10)
local notation "Y" => (Vec2.mk (ZExp.var 2) (ZExp.var 3) : Vec2 10)
local notation "u" => (Vec2.mk (ZExp.var 4) (ZExp.var 5) : Vec2 10)
local notation "v" => (Vec2.mk (ZExp.var 6) (ZExp.var 7) : Vec2 10)
local notation "t" => (ZExp.var 8 : ZExp 10)
local notation "r" => (ZExp.var 9 : ZExp 10)

/-- The difference of two points. -/
def sub2 {k : ℕ} (P Q : Vec2 k) : Vec2 k := ⟨P.x - Q.x, P.y - Q.y⟩

/-- If the point `X + t u` of one line is the point `Y + r v` of another, then
`t det(u, v) = det(Y − X, v)`. -/
theorem sine_law_det :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [((X).x + t * (u).x, (Y).x + r * (v).x), ((X).y + t * (u).y, (Y).y + r * (v).y)]
        (t * det2 u v, det2 (sub2 Y X) v)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [sub2]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 7 * h₁ - ρ 6 * h₂)

/-- `|t u − r v|² = t² u·u + r² v·v − 2 t r u·v`. -/
theorem cosine_expansion :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] ((t * (u).x - r * (v).x) ^ 2 + (t * (u).y - r * (v).y) ^ 2,
        t ^ 2 * dot2 u u + r ^ 2 * dot2 v v - 2 * t * r * dot2 u v)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Lines

end LeanProofs.IPRA.Geometry.MorleyCertificate
