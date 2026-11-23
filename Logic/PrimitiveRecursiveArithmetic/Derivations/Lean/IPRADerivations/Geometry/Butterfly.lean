import IPRADerivations.Core.IntCertificates

/-!
# The butterfly theorem

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorem `circ:butterfly`
("Butterfly theorem with explicit intersection hypotheses"). In the packet's coordinates the midpoint `M` of the
chord `PQ` is the origin, the circle is (B1) `x² + y² − 2 k y = c₀`, and the two chords through `M` are
`A = a u`, `B = b u`, `C = c v`, `D = d v`. The lines `AD` and `BC` meet the axis `PQ` at

  (B3) `x_X = a d Δ / (d v_y − a u_y)`, `x_Y = b c Δ / (c v_y − b u_y)`, `Δ = [u, v]`.

As iPRA derivations for integer terms:

* `butterfly_numerator`: "Adding (B3) over their common denominator gives numerator
  `Δ (c d (a + b) v_y − a b (c + d) u_y)`": `a d (c v_y − b u_y) + b c (d v_y − a u_y) =
  c d (a + b) v_y − a b (c + d) u_y`;
* `butterfly`: from the four circle equations for `A, B, C, D`,
  `|u|² |v|² (a − b)(c − d) · (c d (a + b) v_y − a b (c + d) u_y) = 0`: the numerator of `x_X + x_Y` vanishes
  after multiplication by the factors that the packet cancels through the root sums and products (B2)
  (`|u|², |v|² > 0`, `a ≠ b`, `c ≠ d`). Hence `x_X + x_Y = 0`: `M` is the midpoint of `XY`.

Not derived: the cancellation of those nonzero factors, and the normalization of the coordinates.
-/

namespace LeanProofs.IPRA.Geometry.Butterfly

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The cleared numerator of `x_X + x_Y` vanishes, in every commutative ring. -/
theorem butterfly_ring {R : Type*} [CommRing R] {a b c d k c0 u1 u2 v1 v2 : R}
    (hA : a * a * (u1 * u1 + u2 * u2) - 2 * k * a * u2 = c0)
    (hB : b * b * (u1 * u1 + u2 * u2) - 2 * k * b * u2 = c0)
    (hC : c * c * (v1 * v1 + v2 * v2) - 2 * k * c * v2 = c0)
    (hD : d * d * (v1 * v1 + v2 * v2) - 2 * k * d * v2 = c0) :
    (u1 * u1 + u2 * u2) * (v1 * v1 + v2 * v2) * (a - b) * (c - d) *
      (c * d * (a + b) * v2 - a * b * (c + d) * u2) = 0 := by
  have E1 : (a - b) * ((a + b) * (u1 * u1 + u2 * u2) - 2 * k * u2) = 0 := by
    linear_combination hA - hB
  have E2 : (a - b) * (a * b * (u1 * u1 + u2 * u2) + c0) = 0 := by
    linear_combination b * hA - a * hB
  have E3 : (c - d) * ((c + d) * (v1 * v1 + v2 * v2) - 2 * k * v2) = 0 := by
    linear_combination hC - hD
  have E4 : (c - d) * (c * d * (v1 * v1 + v2 * v2) + c0) = 0 := by
    linear_combination d * hC - c * hD
  linear_combination ((c - d) * c * d * (v1 * v1 + v2 * v2) * v2) * E1 +
    (2 * k * u2 * (a - b) * v2) * E4 - ((c - d) * (c + d) * (v1 * v1 + v2 * v2) * u2) * E2 +
    (c0 * (a - b) * u2) * E3

/-- The numerator of `x_X + x_Y` over the common denominator. -/
theorem butterfly_numerator (a b c d u₂ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a * d * (c * v₂ - b * u₂) + b * c * (d * v₂ - a * u₂))
      (c * d * (a + b) * v₂ - a * b * (c + d) * u₂) := by
  apply ZT.derive
  zsimp
  ring

/-- The butterfly theorem, cleared: the numerator of `x_X + x_Y` times `|u|² |v|² (a − b)(c − d)` vanishes. -/
theorem butterfly {a b c d k c0 u₁ u₂ v₁ v₂ : ZT n}
    (hA : Γ ⊢[PRAAx] ZT.eq (a * a * (u₁ * u₁ + u₂ * u₂) - ZT.natLit 2 * k * a * u₂) c0)
    (hB : Γ ⊢[PRAAx] ZT.eq (b * b * (u₁ * u₁ + u₂ * u₂) - ZT.natLit 2 * k * b * u₂) c0)
    (hC : Γ ⊢[PRAAx] ZT.eq (c * c * (v₁ * v₁ + v₂ * v₂) - ZT.natLit 2 * k * c * v₂) c0)
    (hD : Γ ⊢[PRAAx] ZT.eq (d * d * (v₁ * v₁ + v₂ * v₂) - ZT.natLit 2 * k * d * v₂) c0) :
    Γ ⊢[PRAAx] ZT.eq
      ((u₁ * u₁ + u₂ * u₂) * (v₁ * v₁ + v₂ * v₂) * (a - b) * (c - d) *
        (c * d * (a + b) * v₂ - a * b * (c + d) * u₂)) (ZT.natLit 0) := by
  have eA := ZT.toZ_eq hA
  have eB := ZT.toZ_eq hB
  have eC := ZT.toZ_eq hC
  have eD := ZT.toZ_eq hD
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero] at eA eB eC eD ⊢
  exact butterfly_ring eA eB eC eD

end LeanProofs.IPRA.Geometry.Butterfly
