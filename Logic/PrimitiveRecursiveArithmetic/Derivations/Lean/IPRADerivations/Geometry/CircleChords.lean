import IPRADerivations.Geometry.TriangleCentres
import IPRADerivations.Core.CertificateTactics

/-!
# Chords, Thales' theorem, inversion and Ptolemy's inequality

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorems `circ:chord-midpoint`,
`circ:chord-distance`, `circ:thales`, `circ:tangent`, `circ:inversion` and `circ:ptolemy-inequality`. Points have
two integer-term coordinates, with `dot`, `det`, `nsq` of `Geometry/TriangleCentres`, and `u ⋆ v` is the pair
(complex) multiplication `pm`. As iPRA derivations:

* `chord_midpoint`: "`0 = |B − O|² − |A − O|² = 2 (M − O) · d`" as the identity
  `(A + B − 2O) · (B − A) = |B − O|² − |A − O|²`;
* `chord_distance`, `chord_le_diameter`: (C2) "`|B − A|² = 4 (ρ − |M − O|²)`" as
  `|B − A|² + |A + B − 2O|² = 2 |A − O|² + 2 |B − O|²`, and "Every chord has length at most the diameter";
* `thales`: (C3) "`(A − P) · (C − P) = |P − M|² − ρ`", times `4`;
* `line_circle`: the line–circle equation "`t (t |v|² + 2 (A − O) · v) = 0`" of the tangent theorem, as
  `|A + t v − O|² − |A − O|² = t (t |v|² + 2 (A − O) · v)`;
* `inversion_distance`: "`| |q|² p − |p|² q |² = |p|² |q|² |p − q|²`", the cleared form of (C15);
* `pair_norm`, `ptolemy_identity`: `|u ⋆ v|² = |u|² |v|²` and "`c ⋆ (d − b) = b ⋆ (d − c) + d ⋆ (c − b)`";
* `zle_of_sq_le`: `x² ≤ y²` and `0 ≤ y` give `x ≤ y` for integer terms;
* `ptolemy_inequality`: (C17) "`|C − A| |D − B| ≤ |B − A| |D − C| + |D − A| |C − B|`" with `A = 0`, squared:
  for `s, t ≥ 0` with `s² = |b|² |d − c|²` and `t² = |d|² |c − b|²`, `|c|² |d − b|² ≤ (s + t)²`.

Not derived: the reflection in the perpendicular bisector, the converse statements, and Ptolemy's theorem with its
cyclic-order hypotheses.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CircleChords

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- First coordinate of the pair product `u ⋆ v`. -/
def pm₁ (u₁ u₂ v₁ v₂ : ZT n) : ZT n := u₁ * v₁ - u₂ * v₂

/-- Second coordinate of the pair product `u ⋆ v`. -/
def pm₂ (u₁ u₂ v₁ v₂ : ZT n) : ZT n := u₁ * v₂ + u₂ * v₁

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [dot, det, nsq, pm₁, pm₂, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)
attribute [local ipra_defs] dot det nsq pm₁ pm₂

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Chords and diameters -/

/-- `(A + B − 2O) · (B − A) = |B − O|² − |A − O|²`. -/
theorem chord_midpoint (a₁ a₂ b₁ b₂ o₁ o₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (a₁ + b₁ - ZT.natLit 2 * o₁) (a₂ + b₂ - ZT.natLit 2 * o₂) (b₁ - a₁) (b₂ - a₂))
      (nsq (b₁ - o₁) (b₂ - o₂) - nsq (a₁ - o₁) (a₂ - o₂)) := by
  ipra_lc

/-- `|B − A|² + |A + B − 2O|² = 2 |A − O|² + 2 |B − O|²`. -/
theorem chord_distance (a₁ a₂ b₁ b₂ o₁ o₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (b₁ - a₁) (b₂ - a₂) + nsq (a₁ + b₁ - ZT.natLit 2 * o₁) (a₂ + b₂ - ZT.natLit 2 * o₂))
      (ZT.natLit 2 * nsq (a₁ - o₁) (a₂ - o₂) + ZT.natLit 2 * nsq (b₁ - o₁) (b₂ - o₂)) := by
  ipra_lc

/-- A chord is at most the diameter: `|B − A|² ≤ 2 |A − O|² + 2 |B − O|²` (`= 4ρ` on the circle). -/
theorem chord_le_diameter (a₁ a₂ b₁ b₂ o₁ o₂ : ZT n) :
    Γ ⊢[PRAAx] zle (nsq (b₁ - a₁) (b₂ - a₂))
      (ZT.natLit 2 * nsq (a₁ - o₁) (a₂ - o₂) + ZT.natLit 2 * nsq (b₁ - o₁) (b₂ - o₂)) := by
  ipra_zle (ZT.toZ Γ (a₁ + b₁ - ZT.natLit 2 * o₁) ^ 2 + ZT.toZ Γ (a₂ + b₂ - ZT.natLit 2 * o₂) ^ 2)

/-- Thales: `4 (A − P) · (C − P) = |2P − A − C|² − |C − A|²`. -/
theorem thales (a₁ a₂ c₁ c₂ p₁ p₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * dot (a₁ - p₁) (a₂ - p₂) (c₁ - p₁) (c₂ - p₂))
      (nsq (ZT.natLit 2 * p₁ - a₁ - c₁) (ZT.natLit 2 * p₂ - a₂ - c₂) - nsq (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- The line–circle equation: `|A + t v − O|² − |A − O|² = t (t |v|² + 2 (A − O) · v)`. -/
theorem line_circle (a₁ a₂ o₁ o₂ v₁ v₂ t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (a₁ + t * v₁ - o₁) (a₂ + t * v₂ - o₂) - nsq (a₁ - o₁) (a₂ - o₂))
      (t * (t * nsq v₁ v₂ + ZT.natLit 2 * dot (a₁ - o₁) (a₂ - o₂) v₁ v₂)) := by
  ipra_lc

/-! ## Inversion and the pair product -/

/-- `| |q|² p − |p|² q |² = |p|² |q|² |p − q|²`. -/
theorem inversion_distance (p₁ p₂ q₁ q₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (nsq q₁ q₂ * p₁ - nsq p₁ p₂ * q₁) (nsq q₁ q₂ * p₂ - nsq p₁ p₂ * q₂))
      (nsq p₁ p₂ * nsq q₁ q₂ * nsq (p₁ - q₁) (p₂ - q₂)) := by
  ipra_lc

/-- `|u ⋆ v|² = |u|² |v|²`. -/
theorem pair_norm (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (pm₁ u₁ u₂ v₁ v₂) (pm₂ u₁ u₂ v₁ v₂)) (nsq u₁ u₂ * nsq v₁ v₂) := by
  ipra_lc

/-- `c ⋆ (d − b) = b ⋆ (d − c) + d ⋆ (c − b)`, in both coordinates. -/
theorem ptolemy_identity (b₁ b₂ c₁ c₂ d₁ d₂ : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (pm₁ c₁ c₂ (d₁ - b₁) (d₂ - b₂))
      (pm₁ b₁ b₂ (d₁ - c₁) (d₂ - c₂) + pm₁ d₁ d₂ (c₁ - b₁) (c₂ - b₂))) ∧
    (Γ ⊢[PRAAx] ZT.eq (pm₂ c₁ c₂ (d₁ - b₁) (d₂ - b₂))
      (pm₂ b₁ b₂ (d₁ - c₁) (d₂ - c₂) + pm₂ d₁ d₂ (c₁ - b₁) (c₂ - b₂))) := by
  constructor <;> geo

/-! ## Ptolemy's inequality -/

/-- `x² ≤ y²` and `0 ≤ y` give `x ≤ y`. -/
theorem zle_of_sq_le {x y : ZT n} (hy : Γ ⊢[PRAAx] zle (ZT.natLit 0) y)
    (h : Γ ⊢[PRAAx] zle (ZT.sq x) (ZT.sq y)) : Γ ⊢[PRAAx] zle x y := by
  refine .orE (lt_or_le (y.pos + x.neg) (x.pos + y.neg)) ?_ Prf.hyp0
  have hlt : (lt (y.pos + x.neg) (x.pos + y.neg) :: Γ) ⊢[PRAAx] le (succ (y.pos + x.neg)) (x.pos + y.neg) :=
    Prf.hyp0
  have hy1 := hy.wk (ψ := lt (y.pos + x.neg) (x.pos + y.neg))
  have h1 := h.wk (ψ := lt (y.pos + x.neg) (x.pos + y.neg))
  refine false_of_comb (zsl h1 + sl hlt * sl hlt + 2 * sl hlt * zsl hy1 + 2 * sl hlt + 2 * zsl hy1) ?_
    (nn_add (nn_add (nn_add (nn_add (nn_zsl _) (nn_mul (nn_sl _) (nn_sl _)))
      (nn_mul (nn_mul (nn_ofNat 2) (nn_sl _)) (nn_zsl _))) (nn_mul (nn_ofNat 2) (nn_sl _)))
      (nn_mul (nn_ofNat 2) (nn_zsl _))) _
  simp only [zsl_def, sl_def, ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_zero, Q.mk_add, Q.mk_succ, map_add, map_one]
  simp only [toZ_def]
  ring

/-- Ptolemy's inequality with `A = 0`, squared: `|c|² |d − b|² ≤ (s + t)²` for `s, t ≥ 0` with
`s² = |b|² |d − c|²` and `t² = |d|² |c − b|²`. -/
theorem ptolemy_inequality {b₁ b₂ c₁ c₂ d₁ d₂ s t : ZT n}
    (hs0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) s) (ht0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) t)
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sq s) (nsq b₁ b₂ * nsq (d₁ - c₁) (d₂ - c₂)))
    (ht : Γ ⊢[PRAAx] ZT.eq (ZT.sq t) (nsq d₁ d₂ * nsq (c₁ - b₁) (c₂ - b₂))) :
    Γ ⊢[PRAAx] zle (nsq c₁ c₂ * nsq (d₁ - b₁) (d₂ - b₂)) (ZT.sq (s + t)) := by
  have es := ZT.toZ_eq hs
  have et := ZT.toZ_eq ht
  gsimp at es et
  have hst : Γ ⊢[PRAAx] zle (ZT.natLit 0) (s * t) := by
    ipra_zle (zsl hs0 * zsl ht0)
  have hsq : Γ ⊢[PRAAx] zle
      (ZT.sq (dot (pm₁ b₁ b₂ (d₁ - c₁) (d₂ - c₂)) (pm₂ b₁ b₂ (d₁ - c₁) (d₂ - c₂))
        (pm₁ d₁ d₂ (c₁ - b₁) (c₂ - b₂)) (pm₂ d₁ d₂ (c₁ - b₁) (c₂ - b₂))))
      (ZT.sq (s * t)) := by
    refine zle_of_comb (ZT.toZ Γ (det (pm₁ b₁ b₂ (d₁ - c₁) (d₂ - c₂)) (pm₂ b₁ b₂ (d₁ - c₁) (d₂ - c₂))
        (pm₁ d₁ d₂ (c₁ - b₁) (c₂ - b₂)) (pm₂ d₁ d₂ (c₁ - b₁) (c₂ - b₂))) ^ 2) ?_ (nn_zsq _)
    gsimp
    have eprod := congr (congrArg HMul.hMul es) et
    linear_combination eprod
  have hP := zle_of_sq_le hst hsq
  ipra_zle (2 * zsl hP) with es + et

end LeanProofs.IPRA.Geometry.CircleChords
