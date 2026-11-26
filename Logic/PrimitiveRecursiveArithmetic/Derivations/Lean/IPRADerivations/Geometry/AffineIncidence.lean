import IPRADerivations.Geometry.TriangleCentres

/-!
# Lines, intersections, Pasch, Ceva, Menelaus, affine maps and Desargues

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/affine.tex`, Theorems `aff:line`,
`aff:intersection`, Corollary `aff:parallel`, Theorems `aff:pasch`, `aff:ceva`, `aff:menelaus`, `aff:maps` and
`aff:desargues`. Points have integer-term coordinates; a ratio `d : (1 − d)` is a pair of terms `d`, `dc`, and a
point of a segment is given with its weights and their sum. As iPRA derivations:

* `frame₁`, `frame₂`: "`N(u) v = (u · v) u + [u, v] J u`"; `parallel_multiple₁`, `parallel_multiple₂`: if
  `[u, v] = 0` then `N(u) v = (u · v) u`;
* `cramer₁`, `cramer₂`: "`[w, v] u − [w, u] v = [u, v] w`", the intersection point of two lines;
  `intersection_t`, `intersection_s`: "an intersection obeys `t u − s v = w`; taking determinants with `v, u`
  forces the two parameters"; `parallel_coincide`: if `[u, v] = 0`, an intersection forces `[w, u] = 0`;
* `pasch_on_BP`, `pasch_on_AQ`, `pasch_BP_weights`, `pasch_AQ_weights`, `pasch_pos_BP`, `pasch_pos_AQ`: for
  `m P = (m − r) A + r C`, `k Q = (k − s) B + s C` and `H = r k + s m − r s` (`hw`), the point with
  `H X = s (m − r) A + r (k − s) B + r s C` lies on `B P` and on `A Q` with positive weights of sum `H`;
* `ceva_necessary`: the three line equations give `d e f (x y z) = dc ec fc (x y z)`; `ceva_point_AD`,
  `ceva_point_BE`, `ceva_point_CF`: conversely the point `(d e, dc ec, d ec)` solves them when
  `d e f = dc ec fc`;
* `menelaus_bary`, `menelaus_det`: the determinant of the three division points is
  `(dc ec fc + d e f)` times the determinant of the triangle;
* `map_det`, `map_combination`: "`[T u, T v] = det(T) [u, v]`", and a linear map commutes with combinations;
* `desargues_side`, `desargues_collinear`: "`t_j B_i − t_i B_j = t_j A_i − t_i A_j`" and
  "`t₃ P₁₂ − t₂ P₁₃ + t₁ P₂₃ = 0`", coordinate by coordinate.

Not derived: the divisions by the nonzero determinants, and the case distinctions on their vanishing.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.AffineIncidence

open_ipra
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The common weight `H = r k + s m − r s` of the Pasch point. -/
def hw (r s m k : ZT n) : ZT n := r * k + s * m - r * s

/-- The determinant of a `3 × 3` matrix, by rows. -/
def det3 (a b c d e f g h i : ZT n) : ZT n := a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

local notation:max "ζ" t:max => ZT.toZ Γ t

attribute [local ipra_defs] hw det3 dot det nsq

/-! ## Lines and their intersection -/

/-- `N(u) v = (u · v) u + [u, v] J u`, first coordinate. -/
theorem frame₁ (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂ * v₁) (dot u₁ u₂ v₁ v₂ * u₁ - det u₁ u₂ v₁ v₂ * u₂) := by
  ipra_lc

/-- `N(u) v = (u · v) u + [u, v] J u`, second coordinate. -/
theorem frame₂ (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂ * v₂) (dot u₁ u₂ v₁ v₂ * u₂ + det u₁ u₂ v₁ v₂ * u₁) := by
  ipra_lc

/-- A vector with `[u, v] = 0` is a multiple of `u`, first coordinate. -/
theorem parallel_multiple₁ {u₁ u₂ v₁ v₂ : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ v₁ v₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂ * v₁) (dot u₁ u₂ v₁ v₂ * u₁) := by
  ipra_lc -ζ u₂ * ZT.toZ_eq h

/-- A vector with `[u, v] = 0` is a multiple of `u`, second coordinate. -/
theorem parallel_multiple₂ {u₁ u₂ v₁ v₂ : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ v₁ v₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂ * v₂) (dot u₁ u₂ v₁ v₂ * u₂) := by
  ipra_lc ζ u₁ * ZT.toZ_eq h

/-- `[w, v] u − [w, u] v = [u, v] w`, first coordinate. -/
theorem cramer₁ (u₁ u₂ v₁ v₂ w₁ w₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det w₁ w₂ v₁ v₂ * u₁ - det w₁ w₂ u₁ u₂ * v₁) (det u₁ u₂ v₁ v₂ * w₁) := by
  ipra_lc

/-- `[w, v] u − [w, u] v = [u, v] w`, second coordinate. -/
theorem cramer₂ (u₁ u₂ v₁ v₂ w₁ w₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det w₁ w₂ v₁ v₂ * u₂ - det w₁ w₂ u₁ u₂ * v₂) (det u₁ u₂ v₁ v₂ * w₂) := by
  ipra_lc

/-- An intersection `t u − s v = w` has `t [u, v] = [w, v]`. -/
theorem intersection_t {u₁ u₂ v₁ v₂ w₁ w₂ t s : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (t * u₁ - s * v₁) w₁) (h2 : Γ ⊢[PRAAx] ZT.eq (t * u₂ - s * v₂) w₂) :
    Γ ⊢[PRAAx] ZT.eq (t * det u₁ u₂ v₁ v₂) (det w₁ w₂ v₁ v₂) := by
  ipra_lc ζ v₂ * ZT.toZ_eq h1 - ζ v₁ * ZT.toZ_eq h2

/-- An intersection `t u − s v = w` has `s [u, v] = [w, u]`. -/
theorem intersection_s {u₁ u₂ v₁ v₂ w₁ w₂ t s : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (t * u₁ - s * v₁) w₁) (h2 : Γ ⊢[PRAAx] ZT.eq (t * u₂ - s * v₂) w₂) :
    Γ ⊢[PRAAx] ZT.eq (s * det u₁ u₂ v₁ v₂) (det w₁ w₂ u₁ u₂) := by
  ipra_lc ζ u₂ * ZT.toZ_eq h1 - ζ u₁ * ZT.toZ_eq h2

/-- Parallel lines with a common point coincide: `[w, u] = 0`. -/
theorem parallel_coincide {u₁ u₂ v₁ v₂ w₁ w₂ t s : ZT n}
    (hd : Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ v₁ v₂) (ZT.natLit 0))
    (h1 : Γ ⊢[PRAAx] ZT.eq (t * u₁ - s * v₁) w₁) (h2 : Γ ⊢[PRAAx] ZT.eq (t * u₂ - s * v₂) w₂) :
    Γ ⊢[PRAAx] ZT.eq (det w₁ w₂ u₁ u₂) (ZT.natLit 0) := by
  ipra_lc ζ s * ZT.toZ_eq hd - (ζ u₂ * ZT.toZ_eq h1 - ζ u₁ * ZT.toZ_eq h2)

/-! ## Pasch -/

/-- The weights of the Pasch point on `B P` add up to `H`. -/
theorem pasch_BP_weights (r s m k : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (s * m + r * (k - s)) (hw r s m k) := by
  ipra_lc

/-- The weights of the Pasch point on `A Q` add up to `H`. -/
theorem pasch_AQ_weights (r s m k : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (s * (m - r) + r * k) (hw r s m k) := by
  ipra_lc

/-- The Pasch point is on `B P`: `H X = (s m) P + r (k − s) B`. -/
theorem pasch_on_BP {A B C P X r s m k : ZT n}
    (hP : Γ ⊢[PRAAx] ZT.eq (m * P) ((m - r) * A + r * C))
    (hX : Γ ⊢[PRAAx] ZT.eq (hw r s m k * X) (s * (m - r) * A + r * (k - s) * B + r * s * C)) :
    Γ ⊢[PRAAx] ZT.eq (hw r s m k * X) (s * (m * P) + r * (k - s) * B) := by
  ipra_lc ZT.toZ_eq hX - ζ s * ZT.toZ_eq hP

/-- The Pasch point is on `A Q`: `H X = s (m − r) A + (r k) Q`. -/
theorem pasch_on_AQ {A B C Q X r s m k : ZT n}
    (hQ : Γ ⊢[PRAAx] ZT.eq (k * Q) ((k - s) * B + s * C))
    (hX : Γ ⊢[PRAAx] ZT.eq (hw r s m k * X) (s * (m - r) * A + r * (k - s) * B + r * s * C)) :
    Γ ⊢[PRAAx] ZT.eq (hw r s m k * X) (s * (m - r) * A + r * (k * Q)) := by
  ipra_lc ZT.toZ_eq hX - ζ r * ZT.toZ_eq hQ

/-- The weight of `B` on `B P` is positive. -/
theorem pasch_pos_BP {r s k : ZT n} (hr : Γ ⊢[PRAAx] zle (ZT.natLit 1) r)
    (hsk : Γ ⊢[PRAAx] zle (s + ZT.natLit 1) k) : Γ ⊢[PRAAx] zle (ZT.natLit 1) (r * (k - s)) := by
  ipra_zle (zsl hr * zsl hsk + zsl hr + zsl hsk)

/-- The weight of `A` on `A Q` is positive. -/
theorem pasch_pos_AQ {r s m : ZT n} (hs : Γ ⊢[PRAAx] zle (ZT.natLit 1) s)
    (hrm : Γ ⊢[PRAAx] zle (r + ZT.natLit 1) m) : Γ ⊢[PRAAx] zle (ZT.natLit 1) (s * (m - r)) := by
  ipra_zle (zsl hs * zsl hrm + zsl hs + zsl hrm)

/-! ## Ceva and Menelaus -/

/-- Concurrent cevians: `d e f (x y z) = dc ec fc (x y z)`. -/
theorem ceva_necessary {d dc e ec f fc x y z : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (d * y) (dc * z)) (h2 : Γ ⊢[PRAAx] ZT.eq (ec * x) (e * z))
    (h3 : Γ ⊢[PRAAx] ZT.eq (f * x) (fc * y)) :
    Γ ⊢[PRAAx] ZT.eq (d * e * f * (x * y * z)) (dc * ec * fc * (x * y * z)) := by
  ipra_lc (ζ e * ζ z) * (ζ f * ζ x) * ZT.toZ_eq h1 - (ζ dc * ζ z) * (ζ f * ζ x) * ZT.toZ_eq h2 +
    (ζ dc * ζ z) * (ζ ec * ζ x) * ZT.toZ_eq h3

/-- The point `(d e, dc ec, d ec)` is on the cevian `A D`. -/
theorem ceva_point_AD (d dc ec : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (d * (dc * ec)) (dc * (d * ec)) := by
  ipra_lc

/-- The point `(d e, dc ec, d ec)` is on the cevian `B E`. -/
theorem ceva_point_BE (d e ec : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ec * (d * e)) (e * (d * ec)) := by
  ipra_lc

/-- Under Ceva's condition the point `(d e, dc ec, d ec)` is on the cevian `C F`. -/
theorem ceva_point_CF {d dc e ec f fc : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (d * e * f) (dc * ec * fc)) :
    Γ ⊢[PRAAx] ZT.eq (f * (d * e)) (fc * (dc * ec)) := by
  ipra_lc ZT.toZ_eq h

/-- The barycentric determinant of Menelaus: `dc ec fc + d e f`. -/
theorem menelaus_bary (d dc e ec f fc : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det3 (ZT.natLit 0) dc d e (ZT.natLit 0) ec fc f (ZT.natLit 0))
      (dc * ec * fc + d * e * f) := by
  ipra_lc

/-- The determinant of the three division points, in homogeneous coordinates. -/
theorem menelaus_det (d dc e ec f fc a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det3 (dc * b₁ + d * c₁) (dc * b₂ + d * c₂) (d + dc) (ec * c₁ + e * a₁) (ec * c₂ + e * a₂) (e + ec)
        (fc * a₁ + f * b₁) (fc * a₂ + f * b₂) (f + fc))
      ((dc * ec * fc + d * e * f) *
        det3 a₁ a₂ (ZT.natLit 1) b₁ b₂ (ZT.natLit 1) c₁ c₂ (ZT.natLit 1)) := by
  ipra_lc

/-! ## Affine maps and Desargues -/

/-- `[T u, T v] = det(T) [u, v]`. -/
theorem map_det (t₁₁ t₁₂ t₂₁ t₂₂ u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (t₁₁ * u₁ + t₁₂ * u₂) (t₂₁ * u₁ + t₂₂ * u₂) (t₁₁ * v₁ + t₁₂ * v₂) (t₂₁ * v₁ + t₂₂ * v₂))
      ((t₁₁ * t₂₂ - t₁₂ * t₂₁) * det u₁ u₂ v₁ v₂) := by
  ipra_lc

/-- A linear map commutes with combinations (one row). -/
theorem map_combination (t₁ t₂ r s a₁ a₂ b₁ b₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (t₁ * (r * a₁ + s * b₁) + t₂ * (r * a₂ + s * b₂))
      (r * (t₁ * a₁ + t₂ * a₂) + s * (t₁ * b₁ + t₂ * b₂)) := by
  ipra_lc

/-- `t_j B_i − t_i B_j = t_j A_i − t_i A_j` for `B_i = A_i + t_i O`. -/
theorem desargues_side (a b o ti tj : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (tj * (a + ti * o) - ti * (b + tj * o)) (tj * a - ti * b) := by
  ipra_lc

/-- `t₃ P₁₂ − t₂ P₁₃ + t₁ P₂₃ = 0`. -/
theorem desargues_collinear (a₁ a₂ a₃ t₁ t₂ t₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (t₃ * (t₂ * a₁ - t₁ * a₂) - t₂ * (t₃ * a₁ - t₁ * a₃) + t₁ * (t₃ * a₂ - t₂ * a₃)) (ZT.natLit 0) := by
  ipra_lc

end LeanProofs.IPRA.Geometry.AffineIncidence
