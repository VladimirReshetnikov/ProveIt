import IPRADerivations.Geometry.TriangleCentres

/-!
# The inscribed angle theorem and its companions

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorems `circ:inscribed`,
`circ:cyclic-converse` and `circ:tangent-chord`. Points have two integer-term coordinates, with `dot`, `det`,
`nsq` of `Geometry/TriangleCentres`. For points `A, B, P` of the circle with centre `O` and squared radius `ρ`,
put `a = A − O`, `b = B − O`, `p = P − O`, `u = a − p`, `v = b − p`. As iPRA derivations:

* `inscribed_core`: "`(ā ⋆ b) ⋆ u ⋆ v̄ = ρ ū ⋆ v`", in its two coordinates
  `(a · b)(u · v) + [a, b][u, v] = ρ (u · v)` and `[a, b](u · v) − (a · b)[u, v] = ρ [u, v]`;
* `inscribed_real`, `inscribed_imag`: (C12) in division-free coordinates,
  "`ρ ((u · v)² − [u, v]²) = |u|² |v|² (a · b)`" and "`2 ρ (u · v)[u, v] = |u|² |v|² [a, b]`": the central angle
  is twice the inscribed angle;
* `angle_circle`: (C13) "`|x|² − d · x − k [d, x] = 0`" is the circle with centre `(d + k J d)/2` through `0`:
  `|2x − (d + k J d)|² − |d + k J d|² = 4 (|x|² − d · x − k [d, x])`;
* `angle_circle_fourth`: "It contains `x = 0, d, b` by construction and `x = e` by the ratio equality": with
  `F(x) = |x|² − d · x` and `T(x) = [d, x]`, from `k T(b) = F(b)` and `F(e) T(b) = F(b) T(e)`,
  `T(b) (F(e) − k T(e)) = 0`;
* `tangent_chord_det`: "`[t, v] = −a · v = ρ − a · b = |v|²/2`" for the tangent direction `t = J a` and the
  chord `v = b − a`.

Not derived: the passage from the squared identity to equal or supplementary angles (the side conditions and
the cancellations of `circ:same-segment`), and the normalization by lengths.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.InscribedAngles

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## The inscribed angle -/

/-- The pair identity `(ā ⋆ b) ⋆ u ⋆ v̄ = ρ ū ⋆ v` for `u = a − p`, `v = b − p` on the circle. -/
theorem inscribed_core {a₁ a₂ b₁ b₂ p₁ p₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ)
    (hp : Γ ⊢[PRAAx] ZT.eq (nsq p₁ p₂) ρ) :
    (Γ ⊢[PRAAx] ZT.eq
      (dot a₁ a₂ b₁ b₂ * dot (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂) +
        det a₁ a₂ b₁ b₂ * det (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂))
      (ρ * dot (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂))) ∧
    (Γ ⊢[PRAAx] ZT.eq
      (det a₁ a₂ b₁ b₂ * dot (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂) -
        dot a₁ a₂ b₁ b₂ * det (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂))
      (ρ * det (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂))) := by
  have eA := ZT.toZ_eq ha
  have eB := ZT.toZ_eq hb
  have eP := ZT.toZ_eq hp
  gsimp at eA eB eP
  constructor
  · apply ZT.derive
    gsimp
    linear_combination
      ((ZT.toZ Γ b₁ - ZT.toZ Γ p₁) * ZT.toZ Γ b₁ + (ZT.toZ Γ b₂ - ZT.toZ Γ p₂) * ZT.toZ Γ b₂) * eA +
        (ZT.toZ Γ ρ - (ZT.toZ Γ a₁ * ZT.toZ Γ p₁ + ZT.toZ Γ a₂ * ZT.toZ Γ p₂)) * eB +
        (ZT.toZ Γ a₁ * ZT.toZ Γ b₁ + ZT.toZ Γ a₂ * ZT.toZ Γ b₂ - ZT.toZ Γ ρ) * eP
  · apply ZT.derive
    gsimp
    linear_combination
      ((ZT.toZ Γ b₁ - ZT.toZ Γ p₁) * ZT.toZ Γ b₂ - (ZT.toZ Γ b₂ - ZT.toZ Γ p₂) * ZT.toZ Γ b₁) * eA -
        (ZT.toZ Γ a₁ * ZT.toZ Γ p₂ - ZT.toZ Γ a₂ * ZT.toZ Γ p₁) * eB +
        (ZT.toZ Γ a₁ * ZT.toZ Γ b₂ - ZT.toZ Γ a₂ * ZT.toZ Γ b₁) * eP

/-- (C12), real part: `ρ ((u · v)² − [u, v]²) = |u|² |v|² (a · b)`. -/
theorem inscribed_real {a₁ a₂ b₁ b₂ p₁ p₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ)
    (hp : Γ ⊢[PRAAx] ZT.eq (nsq p₁ p₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq
      (ρ * (ZT.sq (dot (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂)) -
        ZT.sq (det (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂))))
      (nsq (a₁ - p₁) (a₂ - p₂) * nsq (b₁ - p₁) (b₂ - p₂) * dot a₁ a₂ b₁ b₂) := by
  have c1 := ZT.toZ_eq (inscribed_core ha hb hp).1
  have c2 := ZT.toZ_eq (inscribed_core ha hb hp).2
  apply ZT.derive
  gsimp at c1 c2 ⊢
  linear_combination
    (-((ZT.toZ Γ a₁ - ZT.toZ Γ p₁) * (ZT.toZ Γ b₁ - ZT.toZ Γ p₁) +
        (ZT.toZ Γ a₂ - ZT.toZ Γ p₂) * (ZT.toZ Γ b₂ - ZT.toZ Γ p₂))) * c1 +
      ((ZT.toZ Γ a₁ - ZT.toZ Γ p₁) * (ZT.toZ Γ b₂ - ZT.toZ Γ p₂) -
        (ZT.toZ Γ a₂ - ZT.toZ Γ p₂) * (ZT.toZ Γ b₁ - ZT.toZ Γ p₁)) * c2

/-- (C12), imaginary part: `2 ρ (u · v)[u, v] = |u|² |v|² [a, b]`. -/
theorem inscribed_imag {a₁ a₂ b₁ b₂ p₁ p₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ)
    (hp : Γ ⊢[PRAAx] ZT.eq (nsq p₁ p₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * ρ * (dot (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂) *
        det (a₁ - p₁) (a₂ - p₂) (b₁ - p₁) (b₂ - p₂)))
      (nsq (a₁ - p₁) (a₂ - p₂) * nsq (b₁ - p₁) (b₂ - p₂) * det a₁ a₂ b₁ b₂) := by
  have c1 := ZT.toZ_eq (inscribed_core ha hb hp).1
  have c2 := ZT.toZ_eq (inscribed_core ha hb hp).2
  apply ZT.derive
  gsimp at c1 c2 ⊢
  linear_combination
    (-((ZT.toZ Γ a₁ - ZT.toZ Γ p₁) * (ZT.toZ Γ b₁ - ZT.toZ Γ p₁) +
        (ZT.toZ Γ a₂ - ZT.toZ Γ p₂) * (ZT.toZ Γ b₂ - ZT.toZ Γ p₂))) * c2 -
      ((ZT.toZ Γ a₁ - ZT.toZ Γ p₁) * (ZT.toZ Γ b₂ - ZT.toZ Γ p₂) -
        (ZT.toZ Γ a₂ - ZT.toZ Γ p₂) * (ZT.toZ Γ b₁ - ZT.toZ Γ p₁)) * c1

/-! ## The converse circle and the tangent–chord angle -/

/-- (C13): `|2x − (d + k J d)|² − |d + k J d|² = 4 (|x|² − d · x − k [d, x])`. -/
theorem angle_circle (x₁ x₂ d₁ d₂ k : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (ZT.natLit 2 * x₁ - (d₁ - k * d₂)) (ZT.natLit 2 * x₂ - (d₂ + k * d₁)) -
        nsq (d₁ - k * d₂) (d₂ + k * d₁))
      (ZT.natLit 4 * (nsq x₁ x₂ - dot d₁ d₂ x₁ x₂ - k * det d₁ d₂ x₁ x₂)) := by
  geo

/-- The fourth point of the converse criterion: `T(b) (F(e) − k T(e)) = 0`. -/
theorem angle_circle_fourth {b₁ b₂ e₁ e₂ d₁ d₂ k : ZT n}
    (hk : Γ ⊢[PRAAx] ZT.eq (k * det d₁ d₂ b₁ b₂) (nsq b₁ b₂ - dot d₁ d₂ b₁ b₂))
    (hr : Γ ⊢[PRAAx] ZT.eq ((nsq e₁ e₂ - dot d₁ d₂ e₁ e₂) * det d₁ d₂ b₁ b₂)
      ((nsq b₁ b₂ - dot d₁ d₂ b₁ b₂) * det d₁ d₂ e₁ e₂)) :
    Γ ⊢[PRAAx] ZT.eq
      (det d₁ d₂ b₁ b₂ * (nsq e₁ e₂ - dot d₁ d₂ e₁ e₂ - k * det d₁ d₂ e₁ e₂)) (ZT.natLit 0) := by
  have ek := ZT.toZ_eq hk
  have er := ZT.toZ_eq hr
  apply ZT.derive
  gsimp at ek er ⊢
  linear_combination er - (ZT.toZ Γ d₁ * ZT.toZ Γ e₂ - ZT.toZ Γ d₂ * ZT.toZ Γ e₁) * ek

/-- The tangent direction `J a` and the chord `v = b − a`: `2 [J a, v] = |v|²`. -/
theorem tangent_chord_det {a₁ a₂ b₁ b₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * det (-a₂) a₁ (b₁ - a₁) (b₂ - a₂)) (nsq (b₁ - a₁) (b₂ - a₂)) := by
  have eA := ZT.toZ_eq ha
  have eB := ZT.toZ_eq hb
  apply ZT.derive
  gsimp at eA eB ⊢
  linear_combination eA - eB

end LeanProofs.IPRA.Geometry.InscribedAngles
