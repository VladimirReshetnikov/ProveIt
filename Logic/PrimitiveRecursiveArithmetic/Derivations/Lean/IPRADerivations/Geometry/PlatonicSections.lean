import IPRADerivations.Geometry.TetraShadow
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# The exact certificates for the largest sections of the small Platonic solids

Packet: `geometry/platonic_sections_ipra_2026-11-19` (largest planar sections of the Platonic solids), the
tetrahedron, cube and octahedron arguments of `small_solids.tex`, whose inequalities "have fixed finite algebraic
proofs over ordered fields". Over integer terms (rational data cleared of denominators):

* `tetra_decomp` (tetrahedron, quadrilateral sections): for `p = α + δ − αδ − γδ`, `q = β + γ − βγ − γδ`,
  `r = αβ − γδ`: `p = α(1 − δ) + δ(1 − γ)`, `q = β(1 − γ) + γ(1 − δ)`, `p − r = α(1 − β) + δ(1 − α)`,
  `q − r = β(1 − α) + γ(1 − β)` and `1 − (p + q − r) = (α + γ − 1)(β + δ − 1)`;
* `tetra_slack`: with `α = a/(a+c)`, `β = a/(a+d)`, `γ = b/(b+d)`, `δ = b/(b+c)` and
  `Den = (a+c)(a+d)(b+c)(b+d)`, `Den (p + q − r) + (ab − cd)² = Den`, so `p + q − r ≤ 1` (`tetra_le_one`):
  every quadrilateral section has area at most the largest face;
* `cube_slack` (cube, truncated case): for `r = s/t ∈ [0, 1]`,
  `(2 + r²)(1 + 2r)² ≤ 2(1 + r)⁴` (cleared: `s²(3t² + 2ts + 2s(t − s))` is the slack), so the area is at most
  `4√2`;
* `octa_area_vector`: the cleared shoelace identity `(b+c) P'×Q' + (a+b) Q'×R' − (a+c) R'×P' = 2(ab+ac+bc)(a,b,c)`
  for `P' = (b,−a,0)`, `Q' = (c,0,−a)`, `R' = (0,c,−b)`;
* `octa_slack`: `(a² + b² + c²)(ab + ac + bc)² ≤ D²`, `D = (a+b)(a+c)(b+c)`, with the all-positive ten-term
  certificate, so every central section of the octahedron has area at most `2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PlatonicSections

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The tetrahedral decompositions of `p, q, p − r, q − r` and of `1 − (p + q − r)`. -/
theorem tetra_decomp (al be ga de : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (al + de - al * de - ga * de) (al * (ZT.natLit 1 - de) + de * (ZT.natLit 1 - ga))) ∧
    (Γ ⊢[PRAAx] ZT.eq (be + ga - be * ga - ga * de) (be * (ZT.natLit 1 - ga) + ga * (ZT.natLit 1 - de))) ∧
    (Γ ⊢[PRAAx] ZT.eq ((al + de - al * de - ga * de) - (al * be - ga * de))
      (al * (ZT.natLit 1 - be) + de * (ZT.natLit 1 - al))) ∧
    (Γ ⊢[PRAAx] ZT.eq ((be + ga - be * ga - ga * de) - (al * be - ga * de))
      (be * (ZT.natLit 1 - al) + ga * (ZT.natLit 1 - be))) ∧
    (Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 - ((al + de - al * de - ga * de) + (be + ga - be * ga - ga * de) -
      (al * be - ga * de))) ((al + ga - ZT.natLit 1) * (be + de - ZT.natLit 1))) := by
  refine ⟨ZT.derive ?_, ZT.derive ?_, ZT.derive ?_, ZT.derive ?_, ZT.derive ?_⟩ <;>
    (simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]; push_cast; ring)

/-- `Den (p + q − r)` as a polynomial in `a, b, c, d`. -/
abbrev Npqr (a b c d : PTm n) : PTm n :=
  a * a * b * c + a * a * b * d + a * a * c * d + a * b * b * c + a * b * b * d + a * b * c * c + num 4 * a * b * c * d +
    a * b * d * d + a * c * c * d + a * c * d * d + b * b * c * d + b * c * c * d + b * c * d * d

/-- `Den = (a+c)(a+d)(b+c)(b+d)`. -/
abbrev Den (a b c d : PTm n) : PTm n := (a + c) * (a + d) * (b + c) * (b + d)

/-- The tetrahedral slack: `Den (p + q − r) + (ab − cd)² = Den`. -/
theorem tetra_slack (a b c d : PTm n) :
    Γ ⊢[PRAAx] Npqr a b c d + ad (a * b) (c * d) * ad (a * b) (c * d) ≐ Den a b c d := by
  ipra_lc natEq (ad_sq (Γ := Γ) (a * b) (c * d))

/-- `p + q − r ≤ 1`: `Den (p + q − r) ≤ Den`. -/
theorem tetra_le_one (a b c d : PTm n) : Γ ⊢[PRAAx] le (Npqr a b c d) (Den a b c d) :=
  le_of_eq_add (d := ad (a * b) (c * d) * ad (a * b) (c * d)) (tetra_slack a b c d).eqSymm

/-- The cube slack: `(2 + r²)(1 + 2r)² ≤ 2(1 + r)⁴` for `r = s/t ≤ 1`. -/
theorem cube_slack {s t : PTm n} (h : Γ ⊢[PRAAx] le s t) :
    Γ ⊢[PRAAx] le ((num 2 * (t * t) + s * s) * ((t + num 2 * s) * (t + num 2 * s)))
      (num 2 * ((t + s) * (t + s) * ((t + s) * (t + s)))) := by
  ipra_le 𝔟 s ^ 2 * (3 * 𝔟 t ^ 2 + 2 * 𝔟 t * 𝔟 s + 2 * 𝔟 s * sl h)

/-- The octahedral shoelace identity, cleared by `D`. -/
theorem octa_area_vector (a b c : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq ((b + c) * (-a * -a - ZT.natLit 0 * ZT.natLit 0) + (a + b) * (ZT.natLit 0 * -b - -a * c) - (a + c) * (c * ZT.natLit 0 - -b * -a))
      (ZT.natLit 2 * (a * b + a * c + b * c) * a)) ∧
    (Γ ⊢[PRAAx] ZT.eq ((b + c) * (ZT.natLit 0 * c - b * -a) + (a + b) * (-a * ZT.natLit 0 - c * -b) - (a + c) * (-b * b - ZT.natLit 0 * ZT.natLit 0))
      (ZT.natLit 2 * (a * b + a * c + b * c) * b)) ∧
    (Γ ⊢[PRAAx] ZT.eq ((b + c) * (b * ZT.natLit 0 - -a * c) + (a + b) * (c * c - ZT.natLit 0 * ZT.natLit 0) - (a + c) * (ZT.natLit 0 * -a - c * b))
      (ZT.natLit 2 * (a * b + a * c + b * c) * c)) := by
  refine ⟨ZT.derive ?_, ZT.derive ?_, ZT.derive ?_⟩ <;>
    (simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]; push_cast; ring)

/-- The octahedral slack: `(a² + b² + c²)(ab + ac + bc)² ≤ ((a+b)(a+c)(b+c))²`. -/
theorem octa_slack (a b c : PTm n) :
    Γ ⊢[PRAAx] le ((a * a + b * b + c * c) * ((a * b + a * c + b * c) * (a * b + a * c + b * c)))
      ((a + b) * (a + c) * (b + c) * ((a + b) * (a + c) * (b + c))) := by
  ipra_le 2 * (𝔟 a ^ 3 * 𝔟 b ^ 3 + 𝔟 a ^ 3 * 𝔟 c ^ 3 + 𝔟 b ^ 3 * 𝔟 c ^ 3) +
    4 * 𝔟 a * 𝔟 b * 𝔟 c * (𝔟 a ^ 2 * 𝔟 b + 𝔟 a ^ 2 * 𝔟 c + 𝔟 a * 𝔟 b ^ 2 + 𝔟 a * 𝔟 c ^ 2 + 𝔟 b ^ 2 * 𝔟 c +
      𝔟 b * 𝔟 c ^ 2) + 7 * 𝔟 a ^ 2 * 𝔟 b ^ 2 * 𝔟 c ^ 2

end LeanProofs.IPRA.Geometry.PlatonicSections
