import IPRADerivations.Geometry.EuclideanSpace
import IPRADerivations.Core.CertificateTactics

/-!
# Pythagoras and its converse, equilateral triangles, and elementary areas and volumes

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/triangles.tex` (Theorems "Pythagoras and its
converse", "Equilateral triangles on a given segment"), `chapters/polygons.tex` (Theorems `poly:areas`,
`poly:parallel-areas`) and `chapters/solids.tex` (Theorems `sol:sphere-section`, `sol:pyramid`). Points have
integer-term coordinates, with `dot`, `det`, `nsq` of `Geometry/TriangleCentres` and `trip` of
`Geometry/EuclideanSpace`. As iPRA derivations:

* `pythagoras`: for `u = B − A`, `v = C − A` with `u · v = 0`, `|B − C|² = |B − A|² + |C − A|²`;
* `pythagoras_converse`: conversely `|u − v|² = |u|² + |v|²` gives `u · v = 0` (the factor `2` is cancelled);
* `pythagoras_dim`: in every dimension, `u · v = 0` gives `N(u + v) = N(u) + N(v)`: the orthogonal
  decomposition "`N(X − O) = N(X − F) + d²`" of a sphere section;
* `equilateral_AC`, `equilateral_BC`: for a term `s` in the role of `√3` and
  `2 (C − A) = (B − A) + s J (B − A)`: `|2 (C − A)|²` and `|2 (C − B)|²` are `4 |B − A|² + (s² − 3) |B − A|²`
  (the relation `s² = 3` has no integer solution, so it is not assumed: it appears as an explicit term);
* `rectangle_area`: "If `u · v = 0`, the Gram identity gives `[u, v]² = N(u) N(v)`";
* `trapezoid_shoelace`: "The boundary order is `(0, 0), (a, 0), (t + b, h), (t, h)`. Its shoelace sum is
  `a h + b h`, independently of `t`";
* `parallel_area`: "Sliding a third vertex by `t u` leaves `[u, C − A]` unchanged";
* `pyramid_det`: "only the normal component of the apex displacement contributes":
  `[b, c, w + β b + γ c] = [b, c, w]`.

Not derived: the square-root readings of these identities as lengths, areas and volumes.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.ElementaryFigures

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open LeanProofs.IPRA.Geometry.EuclideanSpace (cx trip sum_add_sq)
open Syn
open scoped Fm

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [dot, det, nsq, cx, trip, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)
attribute [local ipra_defs] dot det nsq cx trip

/-! ## Pythagoras -/

/-- A right angle at `A`: `|u − v|² = |u|² + |v|²`. -/
theorem pythagoras {u₁ u₂ v₁ v₂ : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (u₁ - v₁) (u₂ - v₂)) (nsq u₁ u₂ + nsq v₁ v₂) := by
  ipra_lc (-2 : Groth (Q Γ)) * ZT.toZ_eq hp

/-- The converse: `|u − v|² = |u|² + |v|²` gives `u · v = 0`. -/
theorem pythagoras_converse {u₁ u₂ v₁ v₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (nsq (u₁ - v₁) (u₂ - v₂)) (nsq u₁ u₂ + nsq v₁ v₂)) :
    Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  gsimp at e
  have h1 : Γ ⊢[PRAAx] zle (dot u₁ u₂ v₁ v₂) (ZT.natLit 0) := by
    ipra_zle2 0 with e
  have h2 : Γ ⊢[PRAAx] zle (ZT.natLit 0) (dot u₁ u₂ v₁ v₂) := by
    ipra_zle2 0 with -e
  exact le_antisymm h1 h2

/-- Pythagoras in dimension `d`: `u · v = 0` gives `N(u + v) = N(u) + N(v)`. -/
theorem pythagoras_dim {u v : Fin d → ZT n}
    (hp : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => u i * v i) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ZT.sq (u i + v i))
      ((ZT.sumFin fun i => ZT.sq (u i)) + ZT.sumFin fun i => ZT.sq (v i)) := by
  have e := ZT.toZ_eq hp
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at e
  have ex := sum_add_sq (fun i => ZT.toZ Γ (u i)) (fun i => ZT.toZ Γ (v i))
  beta_reduce at ex
  apply ZT.derive
  zsimp
  rw [ex]
  linear_combination (2 : Groth (Q Γ)) * e

/-! ## Equilateral triangles -/

/-- `|u + s J u|² = 4 |u|² + (s² − 3) |u|²`: the side `AC`, of squared length `4 |u|²` on the relation
`s² = 3`. -/
theorem equilateral_AC (u₁ u₂ s : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (u₁ - s * u₂) (u₂ + s * u₁))
      (ZT.natLit 4 * nsq u₁ u₂ + (s * s - ZT.natLit 3) * nsq u₁ u₂) := by
  ipra_lc

/-- `|−u + s J u|² = 4 |u|² + (s² − 3) |u|²`: the side `BC`. -/
theorem equilateral_BC (u₁ u₂ s : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (-u₁ - s * u₂) (-u₂ + s * u₁))
      (ZT.natLit 4 * nsq u₁ u₂ + (s * s - ZT.natLit 3) * nsq u₁ u₂) := by
  ipra_lc

/-! ## Areas and volumes -/

/-- A rectangle: `u · v = 0` gives `[u, v]² = N(u) N(v)`. -/
theorem rectangle_area {u₁ u₂ v₁ v₂ : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sq (det u₁ u₂ v₁ v₂)) (nsq u₁ u₂ * nsq v₁ v₂) := by
  ipra_lc (-(ZT.toZ Γ u₁ * ZT.toZ Γ v₁ + ZT.toZ Γ u₂ * ZT.toZ Γ v₂)) * ZT.toZ_eq hp

/-- The shoelace sum of the trapezoid `(0, 0), (a, 0), (t + b, h), (t, h)` is `a h + b h`. -/
theorem trapezoid_shoelace (a b h t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (ZT.natLit 0) (ZT.natLit 0) a (ZT.natLit 0) + det a (ZT.natLit 0) (t + b) h +
        det (t + b) h t h + det t h (ZT.natLit 0) (ZT.natLit 0))
      (a * h + b * h) := by
  ipra_lc

/-- Sliding the third vertex along the base: `[u, w + t u] = [u, w]`. -/
theorem parallel_area (u₁ u₂ w₁ w₂ t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ (w₁ + t * u₁) (w₂ + t * u₂)) (det u₁ u₂ w₁ w₂) := by
  ipra_lc

/-- The determinant of a pyramid's tetrahedron sees only the component of the apex off the base plane:
`[b, c, w + β b + γ c] = [b, c, w]`. -/
theorem pyramid_det (b₁ b₂ b₃ c₁ c₂ c₃ w₁ w₂ w₃ β γ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (trip b₁ b₂ b₃ c₁ c₂ c₃ (w₁ + β * b₁ + γ * c₁) (w₂ + β * b₂ + γ * c₂) (w₃ + β * b₃ + γ * c₃))
      (trip b₁ b₂ b₃ c₁ c₂ c₃ w₁ w₂ w₃) := by
  ipra_lc

end LeanProofs.IPRA.Geometry.ElementaryFigures
