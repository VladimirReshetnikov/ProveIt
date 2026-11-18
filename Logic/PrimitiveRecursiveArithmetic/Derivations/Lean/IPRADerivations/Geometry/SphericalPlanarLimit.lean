import IPRADerivations.Core.PolynomialInequalities

/-!
# The planar limit with an explicit remainder (`spherical_trigonometry_ipra_2026-11-15`, `thm:planar-limit`)

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, `sections/09_differential_limit.tex`,
theorem `thm:planar-limit`: for `0 ≤ a, b, c ≤ ε ≤ 1` and the exact spherical cosine law,
`|c² − a² − b² + 2ab cos C| ≤ 2ε⁴` (9.5). Proof: with `F(t) = 2(1 − cos t)`,

`c² − a² − b² + 2ab cos C = [c² − F(c)] − [a² − F(a)] − [b² − F(b)] − 2(1 − cos a)(1 − cos b)
   + 2(ab − sin a sin b) cos C`.

"The first line of errors has absolute value at most `3ε⁴/12`. Since `1 − cos t ≤ t²/2`, the
next term is at most `ε⁴/2`. Finally ... the last term is at most `2ε⁴/3`. Their sum is
`17ε⁴/12 < 2ε⁴`." And the corollary (9.10): `|a sin B − b sin A| ≤ ε³/3`, from
"`a sin B − b sin A = (a − sin a) sin B − (b − sin b) sin A`".

The Taylor bounds (9.6), (9.7) are hypotheses; what is derived is the passage from them and
the exact laws to the conclusion, as implications between integer polynomial relations, closed
over all variables (`Core/PolynomialInequalities`: the certificate holds in every commutative
ring with a cone). `E` stands for `ε⁴`, `E₃` for `ε³`:

* `planar_upper`, `planar_lower`: from the cosine law `z = xy + s_a s_b c_C`, the three bounds
  `12 |t² − 2(1 − cos t)| ≤ E`, `0 ≤ 2(1 − x)(1 − y)`, `2 · 2(1 − x)(1 − y) ≤ E` and
  `3 |2(ab − s_a s_b) c_C| ≤ 2E`: `12 (c² − a² − b² + 2ab c_C) ≤ 17 E` and
  `−17 E ≤ 12 (c² − a² − b² + 2ab c_C)`, that is `|…| ≤ 17ε⁴/12`;
* `planar_two`: `17 E ≤ 24 E` from the same hypotheses, so `|…| ≤ 2ε⁴` (9.5);
* `sine_cross_upper`, `sine_cross_lower`: from the sine law `s_a s_B = s_b s_A`,
  `0 ≤ a − s_a`, `6 (a − s_a) ≤ E₃`, the same for `b`, and `0 ≤ s_A, s_B ≤ 1`:
  `6 |a s_B − b s_A| ≤ E₃`, which is sharper than (9.10) (`3 |…| ≤ E₃`).

Not derived: the Taylor bounds (9.6), (9.7) themselves (finite alternating sums for the cosine
and sine names), and the intermediate estimates of the two product terms from them.
-/

namespace LeanProofs.IPRA.Geometry.SphericalPlanarLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The cosine law: ten variables -/

section Cosine

local notation "a" => (ZExp.var 0 : ZExp 10)
local notation "b" => (ZExp.var 1 : ZExp 10)
local notation "c" => (ZExp.var 2 : ZExp 10)
local notation "x" => (ZExp.var 3 : ZExp 10)
local notation "y" => (ZExp.var 4 : ZExp 10)
local notation "z" => (ZExp.var 5 : ZExp 10)
local notation "sa" => (ZExp.var 6 : ZExp 10)
local notation "sb" => (ZExp.var 7 : ZExp 10)
local notation "cC" => (ZExp.var 8 : ZExp 10)
local notation "E" => (ZExp.var 9 : ZExp 10)

/-- `t² − 2(1 − cos t)` for the three sides, the cross term and the sine term. -/
abbrev Uc : ZExp 10 := c ^ 2 - 2 * (1 - z)
abbrev Ua : ZExp 10 := a ^ 2 - 2 * (1 - x)
abbrev Ub : ZExp 10 := b ^ 2 - 2 * (1 - y)
abbrev W : ZExp 10 := 2 * ((1 - x) * (1 - y))
abbrev V : ZExp 10 := 2 * ((a * b - sa * sb) * cC)
/-- The planar defect `c² − a² − b² + 2ab cos C`. -/
abbrev L : ZExp 10 := c ^ 2 - a ^ 2 - b ^ 2 + 2 * (a * b * cC)

/-- The hypotheses of `thm:planar-limit`: the cosine law and the five error bounds. -/
abbrev hyps : List (Rel 10) :=
  [.eq z (x * y + sa * sb * cC),
   .le (12 * Uc) E, .le (-E) (12 * Uc),
   .le (12 * Ua) E, .le (-E) (12 * Ua),
   .le (12 * Ub) E, .le (-E) (12 * Ub),
   .le 0 W, .le (2 * W) E,
   .le (3 * V) (2 * E), .le (-(2 * E)) (3 * V)]

/-- (9.5), upper half: `12 (c² − a² − b² + 2ab cos C) ≤ 17 ε⁴`. -/
theorem planar_upper :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10) (impR hyps (.le (12 * L) (17 * E))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hcos, c1, c2, a1, a2, b1, b2, w0, w2, v1, v2⟩ := h
    exact C.of_eq
      (C.add (C.add (C.add (C.add (C.add c1 a2) b2) (C.mul (C.ofNat 12) w0))
        (C.mul (C.ofNat 4) v1)) (C.mul (C.ofNat 6) (C.add w2 (C.mul (C.ofNat 2) w0))))
      (by linear_combination 24 * hcos))

/-- (9.5), lower half: `−17 ε⁴ ≤ 12 (c² − a² − b² + 2ab cos C)`. -/
theorem planar_lower :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10) (impR hyps (.le (-(17 * E)) (12 * L))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hcos, c1, c2, a1, a2, b1, b2, w0, w2, v1, v2⟩ := h
    exact C.of_eq
      (C.add (C.add (C.add (C.add c2 a1) b1) (C.mul (C.ofNat 6) w2)) (C.mul (C.ofNat 4) v2))
      (by linear_combination (-24) * hcos))

/-- `17 ε⁴ ≤ 24 ε⁴`: the bound `17ε⁴/12` is below `2ε⁴`. -/
theorem planar_two :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10) (impR hyps (.le (17 * E) (24 * E))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hcos, c1, c2, a1, a2, b1, b2, w0, w2, v1, v2⟩ := h
    exact C.of_eq (C.mul (C.ofNat 7) (C.add w2 (C.mul (C.ofNat 2) w0))) (by ring))

end Cosine

/-! ## The sine cross relation: seven variables -/

section Sine

local notation "a" => (ZExp.var 0 : ZExp 7)
local notation "b" => (ZExp.var 1 : ZExp 7)
local notation "sa" => (ZExp.var 2 : ZExp 7)
local notation "sb" => (ZExp.var 3 : ZExp 7)
local notation "sA" => (ZExp.var 4 : ZExp 7)
local notation "sB" => (ZExp.var 5 : ZExp 7)
local notation "E₃" => (ZExp.var 6 : ZExp 7)

/-- The hypotheses of (9.10): the sine law, (9.7) for `a` and `b`, and `0 ≤ sin A, sin B ≤ 1`. -/
abbrev hypsS : List (Rel 7) :=
  [.eq (sa * sB) (sb * sA),
   .le 0 (a - sa), .le (6 * (a - sa)) E₃,
   .le 0 (b - sb), .le (6 * (b - sb)) E₃,
   .le 0 sA, .le sA 1, .le 0 sB, .le sB 1]

/-- (9.10), upper half: `6 (a sin B − b sin A) ≤ ε³`. -/
theorem sine_cross_upper :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (impR hypsS (.le (6 * (a * sB - b * sA)) E₃)) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hsin, a0, a1, b0, b1, A0, A1, B0, B1⟩ := h
    exact C.of_eq
      (C.add (C.add a1 (C.mul (C.ofNat 6) (C.mul a0 B1))) (C.mul (C.ofNat 6) (C.mul b0 A0)))
      (by linear_combination (-6) * hsin))

/-- (9.10), lower half: `−ε³ ≤ 6 (a sin B − b sin A)`. -/
theorem sine_cross_lower :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (impR hypsS (.le (-E₃) (6 * (a * sB - b * sA)))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hsin, a0, a1, b0, b1, A0, A1, B0, B1⟩ := h
    exact C.of_eq
      (C.add (C.add b1 (C.mul (C.ofNat 6) (C.mul b0 A1))) (C.mul (C.ofNat 6) (C.mul a0 B0)))
      (by linear_combination 6 * hsin))

end Sine

end LeanProofs.IPRA.Geometry.SphericalPlanarLimit
