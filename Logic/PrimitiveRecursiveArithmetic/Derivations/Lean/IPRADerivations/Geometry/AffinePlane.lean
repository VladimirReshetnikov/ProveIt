import IPRADerivations.Geometry.TriangleCentres

/-!
# Perpendicular feet, bisectors, reflections and barycentric coordinates

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/affine.tex`, Theorems `aff:foot`,
`aff:bisector`, `aff:reflection`, `aff:barycentric` and `aff:intercept`. Points have two integer-term
coordinates, with `dot`, `det`, `nsq` of `Geometry/TriangleCentres`; for a line `L(A, u)` put `N = |u|²` and
`κ = (P − A) · u`, so that `N F = N A + κ u` is the foot of `P` times `N` (`foot₁`, `foot₂`). As iPRA derivations:

* `foot_perp`: "Taking the dot product of `P − F` with `u` gives zero": `(N P − N F) · u = 0`;
* `foot_distance`, `foot_nearest`: "`N(P − (F + t u)) = N(P − F) + t² N(u)`", times `N²`, and "the foot is the
  unique point of the line nearest to `P`" as `|N (P − F)|² ≤ |N (P − F − t u)|²`;
* `bisector_locus`: "`N(X − A) − N(X − B) = 2 (X − M) · u`" for `M = (A + B)/2`, `u = B − A`;
* `reflection_isometry`: the reflection `R(P) = 2 F(P) − P` preserves squared distances:
  `|N R(P) − N R(Q)|² = N² |P − Q|²`;
* `barycentric`: `D (X − A) = [X − A, C − A] (B − A) + [B − A, X − A] (C − A)` for `D = [B − A, C − A]`, in both
  coordinates: the coordinates `β = [X − A, C − A]/D`, `γ = [B − A, X − A]/D`;
* `subarea_B`, `subarea_C`, `subarea_sum`: "`[C − X, A − X] = β D`, `[A − X, B − X] = γ D`", and the three
  oriented subareas sum to `D` (so `[B − X, C − X] = α D` with `α = 1 − β − γ`);
* `intercept`: "`[s v − t u, v − u] = (s − t) [u, v]`".

Not derived: the uniqueness statements, the involution `R ∘ R = id`, and the sign characterization of the filled
triangle.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.AffinePlane

open_ipra
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- First coordinate of `N F = N A + ((P − A) · u) u`. -/
def foot₁ (p₁ p₂ a₁ a₂ u₁ u₂ : ZT n) : ZT n :=
  nsq u₁ u₂ * a₁ + dot (p₁ - a₁) (p₂ - a₂) u₁ u₂ * u₁

/-- Second coordinate of `N F`. -/
def foot₂ (p₁ p₂ a₁ a₂ u₁ u₂ : ZT n) : ZT n :=
  nsq u₁ u₂ * a₂ + dot (p₁ - a₁) (p₂ - a₂) u₁ u₂ * u₂

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [foot₁, foot₂, dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)
attribute [local ipra_defs] foot₁ foot₂ dot det nsq

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-- `(N P − N F) · u = 0`. -/
theorem foot_perp (p₁ p₂ a₁ a₂ u₁ u₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (nsq u₁ u₂ * p₁ - foot₁ p₁ p₂ a₁ a₂ u₁ u₂)
      (nsq u₁ u₂ * p₂ - foot₂ p₁ p₂ a₁ a₂ u₁ u₂) u₁ u₂) (ZT.natLit 0) := by
  ipra_lc

/-- `|N (P − F − t u)|² = |N (P − F)|² + N² t² N`. -/
theorem foot_distance (p₁ p₂ a₁ a₂ u₁ u₂ t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (nsq u₁ u₂ * p₁ - foot₁ p₁ p₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * t * u₁)
        (nsq u₁ u₂ * p₂ - foot₂ p₁ p₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * t * u₂))
      (nsq (nsq u₁ u₂ * p₁ - foot₁ p₁ p₂ a₁ a₂ u₁ u₂) (nsq u₁ u₂ * p₂ - foot₂ p₁ p₂ a₁ a₂ u₁ u₂) +
        nsq u₁ u₂ * nsq u₁ u₂ * (t * t) * nsq u₁ u₂) := by
  ipra_lc

/-- The foot is the nearest point of the line. -/
theorem foot_nearest (p₁ p₂ a₁ a₂ u₁ u₂ t : ZT n) :
    Γ ⊢[PRAAx] zle
      (nsq (nsq u₁ u₂ * p₁ - foot₁ p₁ p₂ a₁ a₂ u₁ u₂) (nsq u₁ u₂ * p₂ - foot₂ p₁ p₂ a₁ a₂ u₁ u₂))
      (nsq (nsq u₁ u₂ * p₁ - foot₁ p₁ p₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * t * u₁)
        (nsq u₁ u₂ * p₂ - foot₂ p₁ p₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * t * u₂)) := by
  ipra_zle (ZT.toZ Γ (nsq u₁ u₂ * t * u₁) ^ 2 + ZT.toZ Γ (nsq u₁ u₂ * t * u₂) ^ 2)

/-- `|X − A|² − |X − B|² = (2X − A − B) · (B − A)`. -/
theorem bisector_locus (x₁ x₂ a₁ a₂ b₁ b₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - a₁) (x₂ - a₂) - nsq (x₁ - b₁) (x₂ - b₂))
      (dot (ZT.natLit 2 * x₁ - a₁ - b₁) (ZT.natLit 2 * x₂ - a₂ - b₂) (b₁ - a₁) (b₂ - a₂)) := by
  ipra_lc

/-- The reflection `R(P) = 2 F(P) − P` is an isometry: `|N R(P) − N R(Q)|² = N² |P − Q|²`. -/
theorem reflection_isometry (p₁ p₂ q₁ q₂ a₁ a₂ u₁ u₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq
        ((ZT.natLit 2 * foot₁ p₁ p₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * p₁) -
          (ZT.natLit 2 * foot₁ q₁ q₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * q₁))
        ((ZT.natLit 2 * foot₂ p₁ p₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * p₂) -
          (ZT.natLit 2 * foot₂ q₁ q₂ a₁ a₂ u₁ u₂ - nsq u₁ u₂ * q₂)))
      (nsq u₁ u₂ * nsq u₁ u₂ * nsq (p₁ - q₁) (p₂ - q₂)) := by
  ipra_lc

/-- Barycentric coordinates: `D (X − A) = [X − A, C − A] (B − A) + [B − A, X − A] (C − A)`. -/
theorem barycentric (x₁ x₂ a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂) * (x₁ - a₁))
      (det (x₁ - a₁) (x₂ - a₂) (c₁ - a₁) (c₂ - a₂) * (b₁ - a₁) +
        det (b₁ - a₁) (b₂ - a₂) (x₁ - a₁) (x₂ - a₂) * (c₁ - a₁))) ∧
    (Γ ⊢[PRAAx] ZT.eq (det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂) * (x₂ - a₂))
      (det (x₁ - a₁) (x₂ - a₂) (c₁ - a₁) (c₂ - a₂) * (b₂ - a₂) +
        det (b₁ - a₁) (b₂ - a₂) (x₁ - a₁) (x₂ - a₂) * (c₂ - a₂))) := by
  constructor <;> geo

/-- The subarea opposite `B`: `[C − X, A − X] = [X − A, C − A]`. -/
theorem subarea_B (x₁ x₂ a₁ a₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (c₁ - x₁) (c₂ - x₂) (a₁ - x₁) (a₂ - x₂))
      (det (x₁ - a₁) (x₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- The subarea opposite `C`: `[A − X, B − X] = [B − A, X − A]`. -/
theorem subarea_C (x₁ x₂ a₁ a₂ b₁ b₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (a₁ - x₁) (a₂ - x₂) (b₁ - x₁) (b₂ - x₂))
      (det (b₁ - a₁) (b₂ - a₂) (x₁ - a₁) (x₂ - a₂)) := by
  ipra_lc

/-- The three oriented subareas sum to `[B − A, C − A]`. -/
theorem subarea_sum (x₁ x₂ a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (b₁ - x₁) (b₂ - x₂) (c₁ - x₁) (c₂ - x₂) + det (c₁ - x₁) (c₂ - x₂) (a₁ - x₁) (a₂ - x₂) +
        det (a₁ - x₁) (a₂ - x₂) (b₁ - x₁) (b₂ - x₂))
      (det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  ipra_lc

/-- The intercept theorem: `[s v − t u, v − u] = (s − t) [u, v]`. -/
theorem intercept (u₁ u₂ v₁ v₂ s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (s * v₁ - t * u₁) (s * v₂ - t * u₂) (v₁ - u₁) (v₂ - u₂))
      ((s - t) * det u₁ u₂ v₁ v₂) := by
  ipra_lc

end LeanProofs.IPRA.Geometry.AffinePlane
