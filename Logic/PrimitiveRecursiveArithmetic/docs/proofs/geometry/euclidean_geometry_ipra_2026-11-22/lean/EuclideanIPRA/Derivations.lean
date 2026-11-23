import IPRADerivations.Core.Tactic
import IPRADerivations.Core.IntCertificates

/-!
# Euclidean coordinate certificates, in the object theory iPRA

STATUS: candidate integration module; NOT compiled in this environment.
There are no `sorry`, new axioms, or `native_decide` commands in this file.

These theorem types are `Γ ⊢[PRAAx] φ`, not equalities merely asserted in
Lean's ambient real field.  `ipra_ring` and `ipra_zle` are the proof-producing
macros from ProveIt, pinned in README.md.  They return object-theory proofs.
Checking this source against that checkout remains a required formalization
step, and the algebraic-root/geometry translation is a separate step.

Integer terms are pairs of natural-number terms, interpreted as differences.
The generic lemmas below can therefore be specialized to explicit `.var2`
coordinates and universally closed with `closeAll`.
-/

namespace EuclideanIPRA.Derivations

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

abbrev Vec2 (n : ℕ) := ZT n × ZT n

namespace Vec2

def add {n} (u v : Vec2 n) : Vec2 n := (u.1 + v.1, u.2 + v.2)
def sub {n} (u v : Vec2 n) : Vec2 n := (u.1 - v.1, u.2 - v.2)
def scale {n} (a : ZT n) (u : Vec2 n) : Vec2 n := (a*u.1, a*u.2)
def turn {n} (u : Vec2 n) : Vec2 n := (-u.2, u.1)
def dot {n} (u v : Vec2 n) : ZT n := u.1*v.1 + u.2*v.2
def det {n} (u v : Vec2 n) : ZT n := u.1*v.2 - u.2*v.1
def sqnorm {n} (u : Vec2 n) : ZT n := ZT.sq u.1 + ZT.sq u.2
def sqdist {n} (u v : Vec2 n) : ZT n := sqnorm (sub u v)
def cmul {n} (u v : Vec2 n) : Vec2 n :=
  (u.1*v.1-u.2*v.2, u.1*v.2+u.2*v.1)

end Vec2

open Vec2

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem dot_symmetry (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (dot u v) (dot v u) := by
  unfold dot
  ipra_ring

/-- The determinant square is the exact Cauchy--Schwarz slack. -/
theorem lagrange (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm u * sqnorm v)
      (ZT.sq (dot u v) + ZT.sq (det u v)) := by
  unfold sqnorm dot det
  ipra_ring

theorem cauchy_schwarz_squared (u v : Vec2 n) :
    Γ ⊢[PRAAx] zle (ZT.sq (dot u v)) (sqnorm u * sqnorm v) := by
  unfold dot sqnorm
  ipra_zle (ZT.toZ Γ (u.1*v.2-u.2*v.1) ^ 2)

theorem squared_distance_nonnegative (u v : Vec2 n) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) (sqdist u v) := by
  unfold sqdist sqnorm sub
  ipra_zle (ZT.toZ Γ (u.1-v.1)^2 + ZT.toZ Γ (u.2-v.2)^2)

/-- The cosine-law identity; orthogonality gives Pythagoras. -/
theorem polarization (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (sub u v))
      (sqnorm u + sqnorm v - ZT.natLit 2 * dot u v) := by
  unfold sqnorm sub dot
  ipra_ring

theorem parallelogram (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (add u v) + sqnorm (sub u v))
      (ZT.natLit 2 * sqnorm u + ZT.natLit 2 * sqnorm v) := by
  unfold sqnorm add sub
  ipra_ring

/-- Twice the median-length formula, with no divisions. -/
theorem apollonius (u v w : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * sqdist u w + ZT.natLit 2 * sqdist v w)
      (sqdist u v + sqnorm (sub (add u v) (scale (ZT.natLit 2) w))) := by
  unfold sqdist sqnorm sub add scale
  ipra_ring

theorem quarter_turn_norm (u : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (turn u)) (sqnorm u) := by
  unfold sqnorm turn
  ipra_ring

theorem quarter_turn_orthogonal (u : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (dot u (turn u)) (ZT.natLit 0) := by
  unfold dot turn
  ipra_ring

theorem complex_norm (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (cmul u v)) (sqnorm u * sqnorm v) := by
  unfold sqnorm cmul
  ipra_ring

theorem determinant_bilinearity (u v w : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (det (add u v) w) (det u w + det v w) := by
  unfold det add
  ipra_ring

theorem shoelace_triangle (u v w : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (det (sub v u) (sub w u))
      (det u v + det v w + det w u) := by
  unfold det sub
  ipra_ring

/-- Numerators in Cramer's rule, x-coordinate. -/
theorem cramer_x (u v w : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (det w v * u.1 + det u w * v.1)
      (det u v * w.1) := by
  unfold det
  ipra_ring

/-- Numerators in Cramer's rule, y-coordinate. -/
theorem cramer_y (u v w : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (det w v * u.2 + det u w * v.2)
      (det u v * w.2) := by
  unfold det
  ipra_ring

theorem area_interpolation (u v w : Vec2 n) (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (sub v u) (sub (add u (scale t (sub w u))) u))
      (t * det (sub v u) (sub w u)) := by
  unfold det add sub scale
  ipra_ring

/-- Heron's squared identity without roots or denominators. -/
theorem heron_coordinate (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * sqnorm u * sqnorm v
        + ZT.natLit 2 * sqnorm v * sqnorm (sub u v)
        + ZT.natLit 2 * sqnorm (sub u v) * sqnorm u
        - ZT.sq (sqnorm u) - ZT.sq (sqnorm v) - ZT.sq (sqnorm (sub u v)))
      (ZT.natLit 4 * ZT.sq (det u v)) := by
  unfold sqnorm sub det
  ipra_ring

/-- Stewart's theorem with an affine division parameter. -/
theorem stewart_affine (u v w : Vec2 n) (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (sqnorm (sub w (add (scale (ZT.natLit 1-t) u) (scale t v)))
        + t*(ZT.natLit 1-t)*sqnorm (sub v u))
      ((ZT.natLit 1-t)*sqnorm (sub w u)+t*sqnorm (sub w v)) := by
  unfold sqnorm add sub scale
  ipra_ring

/-- Vanishing of either side gives the other direction of Thales' theorem. -/
theorem thales_identity (a b p : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 4 * dot (sub p a) (sub p b))
      (sqnorm (sub (scale (ZT.natLit 2) p) (add a b)) - sqnorm (sub a b)) := by
  unfold dot sub add scale sqnorm
  ipra_ring

/-- Reflection numerator, with q(u)^2 as the common scale factor. -/
theorem reflection_norm (u w : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (sqnorm (sub (scale (ZT.natLit 2*dot w u) u) (scale (sqnorm u) w)))
      (ZT.sq (sqnorm u) * sqnorm w) := by
  unfold sqnorm sub scale dot
  ipra_ring

theorem projection_perpendicular (a v p : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (dot (sub (scale (sqnorm v) p)
        (add (scale (sqnorm v) a) (scale (dot (sub p a) v) v))) v)
      (ZT.natLit 0) := by
  unfold dot sqnorm sub scale add
  ipra_ring

/-- Twice the circumcenter times det(u,v), with A chosen as the origin. -/
def circumNumerator (u v : Vec2 n) : Vec2 n :=
  sub (scale (sqnorm v) (turn u)) (scale (sqnorm u) (turn v))

theorem circumcenter_first (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (dot (circumNumerator u v) u) (sqnorm u * det u v) := by
  unfold dot circumNumerator sqnorm sub scale turn det
  ipra_ring

theorem circumcenter_second (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (dot (circumNumerator u v) v) (sqnorm v * det u v) := by
  unfold dot circumNumerator sqnorm sub scale turn det
  ipra_ring

theorem circumradius_numerator (u v : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (circumNumerator u v))
      (sqnorm u * sqnorm v * sqnorm (sub u v)) := by
  unfold sqnorm circumNumerator sub scale turn
  ipra_ring

theorem orthocenter_identity (a b c : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (dot (sub (add (add a b) c) a) (sub b c))
      (sqnorm b - sqnorm c) := by
  unfold dot sub add sqnorm
  ipra_ring

theorem nine_point_midpoint (a b c : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (sub (add a b) (add (add a b) c))) (sqnorm c) := by
  unfold sqnorm add sub
  ipra_ring

theorem line_circle_expansion (p o v : Vec2 n) (t r : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (sub (add p (scale t v)) o) - ZT.sq r)
      (sqnorm v * ZT.sq t + ZT.natLit 2 * dot (sub p o) v * t
        + sqnorm (sub p o) - ZT.sq r) := by
  unfold sqnorm sub add scale dot
  ipra_ring

theorem radical_axis (p o c : Vec2 n) (r s : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      ((sqnorm (sub p o) - ZT.sq r) - (sqnorm (sub p c) - ZT.sq s))
      (ZT.natLit 2 * dot p (sub c o) + sqnorm o - sqnorm c - ZT.sq r + ZT.sq s) := by
  unfold sqnorm sub dot
  ipra_ring

theorem ptolemy_complex_x (a b c d : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq ((cmul (sub a c) (sub b d)).1)
      ((cmul (sub a b) (sub c d)).1 + (cmul (sub a d) (sub b c)).1) := by
  unfold cmul sub
  ipra_ring

theorem ptolemy_complex_y (a b c d : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq ((cmul (sub a c) (sub b d)).2)
      ((cmul (sub a b) (sub c d)).2 + (cmul (sub a d) (sub b c)).2) := by
  unfold cmul sub
  ipra_ring

theorem varignon_area (a b c d : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (add a b) (add b c) + det (add b c) (add c d)
        + det (add c d) (add d a) + det (add d a) (add a b))
      (ZT.natLit 2 * (det a b + det b c + det c d + det d a)) := by
  unfold det add
  ipra_ring

theorem leibniz_centroid (a b c x : Vec2 n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 3 * (sqdist x a + sqdist x b + sqdist x c))
      (sqnorm (sub (scale (ZT.natLit 3) x) (add (add a b) c))
        + sqdist a b + sqdist b c + sqdist c a) := by
  unfold sqdist sqnorm sub scale add
  ipra_ring

theorem weighted_norm (a b c : Vec2 n) (r s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (sqnorm (add (add (scale r a) (scale s b)) (scale t c)))
      ((r+s+t)*(r*sqnorm a+s*sqnorm b+t*sqnorm c)
        -r*s*sqdist a b-s*t*sqdist b c-t*r*sqdist c a) := by
  unfold sqdist sqnorm sub scale add
  ipra_ring

theorem side_angle_numerator (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (a*(ZT.sq b+ZT.sq c-ZT.sq a)-b*(ZT.sq a+ZT.sq c-ZT.sq b))
      ((a-b)*(ZT.sq c-ZT.sq (a+b))) := by
  ipra_ring

theorem heron_side_factor (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 4 * ZT.sq b * ZT.sq c-ZT.sq (ZT.sq b+ZT.sq c-ZT.sq a))
      ((a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c)) := by
  ipra_ring

/-! ## Three-dimensional identities -/

abbrev Vec3 (n : ℕ) := ZT n × ZT n × ZT n

namespace Vec3

def dot {n} (u v : Vec3 n) : ZT n := u.1*v.1 + u.2.1*v.2.1 + u.2.2*v.2.2
def sqnorm {n} (u : Vec3 n) : ZT n := ZT.sq u.1 + ZT.sq u.2.1 + ZT.sq u.2.2
def scale {n} (t : ZT n) (u : Vec3 n) : Vec3 n := (t*u.1, t*u.2.1, t*u.2.2)
def cross {n} (u v : Vec3 n) : Vec3 n :=
  (u.2.1*v.2.2-u.2.2*v.2.1, u.2.2*v.1-u.1*v.2.2, u.1*v.2.1-u.2.1*v.1)
def triple {n} (u v w : Vec3 n) : ZT n := dot u (cross v w)

end Vec3

theorem lagrange_three (u v : Vec3 n) :
    Γ ⊢[PRAAx] ZT.eq (Vec3.sqnorm (Vec3.cross u v))
      (Vec3.sqnorm u * Vec3.sqnorm v - ZT.sq (Vec3.dot u v)) := by
  unfold Vec3.sqnorm Vec3.cross Vec3.dot
  ipra_ring

theorem cross_perpendicular_first (u v : Vec3 n) :
    Γ ⊢[PRAAx] ZT.eq (Vec3.dot u (Vec3.cross u v)) (ZT.natLit 0) := by
  unfold Vec3.dot Vec3.cross
  ipra_ring

theorem cross_perpendicular_second (u v : Vec3 n) :
    Γ ⊢[PRAAx] ZT.eq (Vec3.dot v (Vec3.cross u v)) (ZT.natLit 0) := by
  unfold Vec3.dot Vec3.cross
  ipra_ring

theorem triple_cyclic (u v w : Vec3 n) :
    Γ ⊢[PRAAx] ZT.eq (Vec3.triple u v w) (Vec3.triple v w u) := by
  unfold Vec3.triple Vec3.dot Vec3.cross
  ipra_ring

theorem volume_scaling (u v w : Vec3 n) (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (Vec3.triple (Vec3.scale t u) (Vec3.scale t v) (Vec3.scale t w))
      (t*t*t*Vec3.triple u v w) := by
  unfold Vec3.triple Vec3.dot Vec3.cross Vec3.scale
  ipra_ring

theorem gram_determinant_three (u v w : Vec3 n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sq (Vec3.triple u v w))
      (Vec3.sqnorm u * Vec3.sqnorm v * Vec3.sqnorm w
        + ZT.natLit 2 * Vec3.dot u v * Vec3.dot v w * Vec3.dot w u
        - Vec3.sqnorm u * ZT.sq (Vec3.dot v w)
        - Vec3.sqnorm v * ZT.sq (Vec3.dot w u)
        - Vec3.sqnorm w * ZT.sq (Vec3.dot u v)) := by
  unfold Vec3.triple Vec3.dot Vec3.cross Vec3.sqnorm
  ipra_ring

/-! ## Explicit closed object-theory formulas -/

abbrev U : Vec2 8 := (.var2 0 1, .var2 2 3)
abbrev V : Vec2 8 := (.var2 4 5, .var2 6 7)

def lagrangeFormula : Fm PTm 8 :=
  ZT.eq (sqnorm U * sqnorm V) (ZT.sq (dot U V) + ZT.sq (det U V))

theorem lagrange_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 lagrangeFormula :=
  closeAll 8 (lagrange U V)

def cauchyFormula : Fm PTm 8 := zle (ZT.sq (dot U V)) (sqnorm U * sqnorm V)

theorem cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 cauchyFormula :=
  closeAll 8 (cauchy_schwarz_squared U V)

end EuclideanIPRA.Derivations
