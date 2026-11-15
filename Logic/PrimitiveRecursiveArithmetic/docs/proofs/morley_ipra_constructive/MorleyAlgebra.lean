import Mathlib

/-!
# Constructive algebraic kernel for Morley's trisector theorem

This file isolates the polynomial and vector identities used by the
accompanying paper.  It deliberately avoids `Real.sin`, `Real.cos`, choice,
compactness, and completeness.  The intended next step is reification of these
ring calculations into `ConciseIPRA.PR` terms.

The file contains no proof placeholders or custom axioms.  It was written against ordinary
Mathlib syntax, but the delivery environment did not contain Lean, so it was
not compiled here; see `README.md` for the exact status.
-/

namespace MorleyIPRA

section Algebra

variable {K : Type*} [LinearOrderedField K]

abbrev Rot (K : Type*) := K × K

/-- Multiplication of unit direction pairs: algebraic angle addition. -/
def rotMul (z w : Rot K) : Rot K :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Algebraic conjugation of a direction pair. -/
def rotConj (z : Rot K) : Rot K := (z.1, -z.2)

/-- Squared norm of a direction pair. -/
def rotNormSq (z : Rot K) : K := z.1 ^ 2 + z.2 ^ 2

/-- The square and cube for `rotMul` (not the componentwise product on pairs). -/
def rotSq (z : Rot K) : Rot K := rotMul z z
def rotCube (z : Rot K) : Rot K := rotMul (rotSq z) z

@[simp] theorem rotMul_one (z : Rot K) : rotMul z (1, 0) = z := by
  ext <;> simp [rotMul]

@[simp] theorem one_rotMul (z : Rot K) : rotMul (1, 0) z = z := by
  ext <;> simp [rotMul]

theorem rotMul_assoc (a b c : Rot K) :
    rotMul (rotMul a b) c = rotMul a (rotMul b c) := by
  ext <;> simp [rotMul] <;> ring

theorem rotMul_comm (a b : Rot K) : rotMul a b = rotMul b a := by
  ext <;> simp [rotMul] <;> ring

theorem rotConj_mul_self (z : Rot K) :
    rotMul (rotConj z) z = (rotNormSq z, 0) := by
  ext <;> simp [rotMul, rotConj, rotNormSq] <;> ring

/-- `rho = 2 sin(60°)` satisfies `rho^2 = 3`. -/
theorem rho_sq_three
    (u : Rot K)
    (hhalf : 2 * u.1 = 1)
    (hunit : rotNormSq u = 1) :
    (2 * u.2) ^ 2 = 3 := by
  rcases u with ⟨cu, su⟩
  simp [rotNormSq] at hhalf hunit ⊢
  have hcu : cu = (1 : K) / 2 := by linarith
  rw [hcu] at hunit
  nlinarith

/-- Algebraic form of `sin(x+60°)`. -/
theorem im_rotMul_sixty
    (z u : Rot K)
    (hhalf : 2 * u.1 = 1) :
    2 * (rotMul z u).2 = z.2 + (2 * u.2) * z.1 := by
  simp [rotMul]
  linear_combination z.2 * hhalf

/-- Algebraic form of `sin(x+120°)`. -/
theorem im_rotMul_sixty_sq
    (z u : Rot K)
    (hhalf : 2 * u.1 = 1)
    (hunit : rotNormSq u = 1) :
    2 * (rotMul z (rotSq u)).2 = -z.2 + (2 * u.2) * z.1 := by
  rcases z with ⟨c, s⟩
  rcases u with ⟨cu, su⟩
  simp [rotMul, rotSq, rotNormSq] at hhalf hunit ⊢
  linear_combination
    (2 * c * su + s * (2 * cu + 1)) * hhalf - 2 * s * hunit

/-- A positive sixty-degree unit pair cubes to the half turn.  Positivity is
not needed for the equation; it selects the intended square root semantically. -/
theorem sixty_cube
    (u : Rot K)
    (hhalf : 2 * u.1 = 1)
    (hunit : rotNormSq u = 1) :
    rotCube u = (-1, 0) := by
  rcases u with ⟨cu, su⟩
  simp [rotNormSq] at hhalf hunit
  apply Prod.ext
  · dsimp [rotCube, rotSq, rotMul]
    linear_combination
      (2 * cu ^ 2 + cu - 1) * hhalf - 3 * cu * hunit
  · dsimp [rotCube, rotSq, rotMul]
    linear_combination su * (2 * cu + 1) * hhalf - su * hunit

/-- If the three one-third rotations multiply to the sixty-degree rotation,
then the two shifted rotations at `B` and `C` add to `pi-alpha`:
`(b*u)*(g*u) = -conj(a)`. -/
theorem morley_angle_sum_pair
    (a b g u : Rot K)
    (ha : rotNormSq a = 1)
    (habg : rotMul (rotMul a b) g = u)
    (hu3 : rotCube u = (-1, 0)) :
    rotMul (rotMul b u) (rotMul g u) = (-a.1, a.2) := by
  have hbg : rotMul b g = rotMul (rotConj a) u := by
    calc
      rotMul b g = rotMul (rotMul (rotConj a) a) (rotMul b g) := by
        rw [rotConj_mul_self, ha]
        simp
      _ = rotMul (rotConj a) (rotMul (rotMul a b) g) := by
        ext <;> simp [rotMul, rotConj] <;> ring
      _ = rotMul (rotConj a) u := by rw [habg]
  calc
    rotMul (rotMul b u) (rotMul g u)
        = rotMul (rotMul b g) (rotMul u u) := by
            ext <;> simp [rotMul] <;> ring
    _ = rotMul (rotMul (rotConj a) u) (rotMul u u) := by rw [hbg]
    _ = rotMul (rotConj a) (rotCube u) := by
          ext <;> simp [rotMul, rotCube, rotSq, rotConj] <;> ring
    _ = rotMul (rotConj a) (-1, 0) := by rw [hu3]
    _ = (-a.1, a.2) := by
          ext <;> simp [rotMul, rotConj]

/-- The shifted form of the triple-angle identity.  Here `rho^2 = 3`, so
`(s + rho*c)/2` and `(-s + rho*c)/2` are the algebraic sines of
`x + 60°` and `x + 120°` when `(c,s)` is a unit direction pair. -/
theorem shifted_triple_angle
    (s c rho : K)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hrho : rho ^ 2 = 3) :
    4 * s * ((s + rho * c) / 2) * ((-s + rho * c) / 2)
      = 3 * s - 4 * s ^ 3 := by
  have hrc : (rho * c) ^ 2 = 3 * c ^ 2 := by
    calc
      (rho * c) ^ 2 = rho ^ 2 * c ^ 2 := by ring
      _ = 3 * c ^ 2 := by rw [hrho]
  have hc : c ^ 2 = 1 - s ^ 2 := by linarith
  calc
    4 * s * ((s + rho * c) / 2) * ((-s + rho * c) / 2)
        = s * ((rho * c) ^ 2 - s ^ 2) := by ring
    _ = s * (3 * c ^ 2 - s ^ 2) := by rw [hrc]
    _ = 3 * s - 4 * s ^ 3 := by rw [hc]; ring

/-- The only nontrivial cosine-law simplification in the proof.

`(cx,sx)` and `(cy,sy)` are unit direction pairs for `x` and `y`.
The last two hypotheses say `x+y = pi-alpha` in algebraic form. -/
theorem morley_bracket
    (sx cx sy cy sa ca : K)
    (hx : cx ^ 2 + sx ^ 2 = 1)
    (hy : cy ^ 2 + sy ^ 2 = 1)
    (hcos : cx * cy - sx * sy = -ca)
    (hsin : sx * cy + cx * sy = sa) :
    sx ^ 2 + sy ^ 2 - 2 * sx * sy * ca = sa ^ 2 := by
  have hca : ca = -(cx * cy - sx * sy) := by linarith
  have hsa : sa = sx * cy + cx * sy := by linarith
  rw [hca, hsa]
  calc
    sx ^ 2 + sy ^ 2 - 2 * sx * sy * (-(cx * cy - sx * sy))
        = (sx * cy + cx * sy) ^ 2
          + sx ^ 2 * (1 - (cy ^ 2 + sy ^ 2))
          + sy ^ 2 * (1 - (cx ^ 2 + sx ^ 2)) := by ring
    _ = (sx * cy + cx * sy) ^ 2 := by rw [hx, hy]; ring

/-- Dot product on algebraic coordinate pairs. -/
def dot (u v : K × K) : K := u.1 * v.1 + u.2 * v.2

/-- Determinant on algebraic coordinate pairs. -/
def det (u v : K × K) : K := u.1 * v.2 - u.2 * v.1

/-- Squared Euclidean distance; this is the right primitive notion for iPRA. -/
def sqDist (p q : K × K) : K :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A point at signed parameter `t` on the ray with origin `p` and direction `u`. -/
def rayPoint (p : K × K) (t : K) (u : K × K) : K × K :=
  (p.1 + t * u.1, p.2 + t * u.2)

/-- Taking determinants of a ray-incidence equation extracts the sine-law
relation without division. -/
theorem det_of_ray_incidence
    (x y u v : K × K) (t w : K)
    (h : rayPoint x t u = rayPoint y w v) :
    t * det u v = det (y.1 - x.1, y.2 - x.2) v := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [rayPoint] at hx hy
  simp [det]
  linear_combination v.2 * hx - v.1 * hy

/-- Polynomial form of the cosine law for two rays with a common origin. -/
theorem sqDist_two_rays
    (p u v : K × K) (t w : K) :
    sqDist (rayPoint p t u) (rayPoint p w v)
      = t ^ 2 * dot u u + w ^ 2 * dot v v - 2 * t * w * dot u v := by
  simp [sqDist, rayPoint, dot]
  ring

/-- Local Morley-side identity after the two adjacent trisector lengths have
been reduced to `k*sin(y)` and `k*sin(x)`. -/
theorem local_morley_side_sq
    (k sx cx sy cy sa ca : K)
    (hx : cx ^ 2 + sx ^ 2 = 1)
    (hy : cy ^ 2 + sy ^ 2 = 1)
    (hcos : cx * cy - sx * sy = -ca)
    (hsin : sx * cy + cx * sy = sa) :
    (k * sy) ^ 2 + (k * sx) ^ 2 - 2 * (k * sy) * (k * sx) * ca
      = (k * sa) ^ 2 := by
  have h := morley_bracket sx cx sy cy sa ca hx hy hcos hsin
  calc
    (k * sy) ^ 2 + (k * sx) ^ 2 - 2 * (k * sy) * (k * sx) * ca
        = k ^ 2 * (sx ^ 2 + sy ^ 2 - 2 * sx * sy * ca) := by ring
    _ = k ^ 2 * sa ^ 2 := by rw [h]
    _ = (k * sa) ^ 2 := by ring

end Algebra

end MorleyIPRA
