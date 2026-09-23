import Surreal.Surcomplex.PolarRoots
import Surreal.Surcomplex.CircleChords

/-!
# Finite regular polygons at arbitrary surreal scales

The vertices are the actual points `O + R*cis(2*pi*k/n)`, with a proved
closing edge and distinct indices in `Fin n`. Perimeter is the finite
sum of their edge lengths; area is the finite sum of their positively
oriented center-triangle areas. Their exact formulas prove
`trigonometry:cor:polygon` for every positive actual surreal radius.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

namespace RegularPolygon

/-- The natural-number vertex sequence, whose first `n` terms are the finite polygon. -/
def vertex (O : Surcomplex.{u}) (R : SignSequence.{u}) (n k : ℕ) : Surcomplex.{u} :=
  circlePoint O R (SignSequence.finiteOfReal (2 * Real.pi * k / n))

/-- The actual polygon vertices are powers of the primitive ordinary sampling root. -/
theorem vertex_eq_zeta (O : Surcomplex.{u}) (R : SignSequence.{u}) (n k : ℕ) :
    vertex O R n k = O + ofReal R * FiniteFourier.zeta n ^ k := by
  have hp : finitePhase (SignSequence.finiteOfReal (2 * Real.pi * k / n)) =
      FiniteFourier.zeta.{u} n ^ k := by
    rw [FiniteFourier.zeta, ← finitePhase_nsmul]
    congr 1
    rw [nsmul_eq_mul, ← map_natCast SignSequence.finiteOfReal k, ← map_mul]
    congr 1
    ring
  exact congrArg (fun z : Surcomplex.{u} => O + ofReal R * z) hp

@[simp] theorem vertex_zero (O : Surcomplex.{u}) (R : SignSequence.{u}) (n : ℕ) :
    vertex O R n 0 = O + ofReal R := by rw [vertex_eq_zeta, pow_zero, mul_one]

/-- The vertex sequence repeats after exactly one ordinary full turn. -/
theorem vertex_periodic (O : Surcomplex.{u}) (R : SignSequence.{u}) (n : ℕ)
    (hn : 0 < n) (k : ℕ) : vertex O R n (k + n) = vertex O R n k := by
  rw [vertex_eq_zeta, vertex_eq_zeta, pow_add,
    (FiniteFourier.isPrimitiveRoot_zeta hn).pow_eq_one, mul_one]

/-- The last edge in the finite edge sum returns to the initial vertex. -/
theorem vertex_closing (O : Surcomplex.{u}) (R : SignSequence.{u}) (n : ℕ)
    (hn : 0 < n) : vertex O R n n = vertex O R n 0 := by
  simpa only [zero_add] using vertex_periodic O R n hn 0

/-- A nonzero radius gives exactly `n` distinct vertices indexed by `Fin n`. -/
theorem vertex_injective (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : R ≠ 0)
    (n : ℕ) (hn : 0 < n) : Function.Injective (fun k : Fin n => vertex O R n k.val) := by
  intro k l he
  change vertex O R n k.val = vertex O R n l.val at he
  rw [vertex_eq_zeta, vertex_eq_zeta] at he
  have hp := mul_left_cancel₀ ((map_ne_zero ofReal).mpr hR) (add_left_cancel he)
  exact Fin.ext ((FiniteFourier.isPrimitiveRoot_zeta hn).pow_inj k.isLt l.isLt hp)

/-- Every vertex is on the actual circle of the specified nonnegative radius. -/
theorem vertex_radius (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 ≤ R)
    (n k : ℕ) : modulus (vertex O R n k - O) = R :=
  modulus_circlePoint_sub_center O R hR _

/-- Every consecutive edge has the exact side length in the source corollary. -/
theorem side_length (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    modulus (vertex O R n (k + 1) - vertex O R n k) =
      2 * R * finiteSin (SignSequence.finiteOfReal (Real.pi / n)) := by
  rw [vertex_eq_zeta, vertex_eq_zeta]
  simpa only [mul_one] using regularPolygon_side_length O 1 modulus_one R hR n hn k

/-- The closing edge has that same side length. -/
theorem closing_edge_length (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (n : ℕ) (hn : 3 ≤ n) :
    modulus (vertex O R n 0 - vertex O R n (n - 1)) =
      2 * R * finiteSin (SignSequence.finiteOfReal (Real.pi / n)) := by
  have he := side_length O R hR n hn (n - 1)
  rw [Nat.sub_add_cancel (by omega), vertex_closing O R n (by omega)] at he
  exact he

/-- Perimeter is the sum of the `n` actual edge lengths, including the closing edge. -/
def perimeter (O : Surcomplex.{u}) (R : SignSequence.{u}) (n : ℕ) : SignSequence.{u} :=
  ∑ k ∈ Finset.range n, modulus (vertex O R n (k + 1) - vertex O R n k)

/-- Summing the finite equal edges gives the exact perimeter at every actual radius. -/
theorem perimeter_eq (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (n : ℕ) (hn : 3 ≤ n) :
    perimeter O R n = 2 * (n : SignSequence.{u}) * R *
      finiteSin (SignSequence.finiteOfReal (Real.pi / n)) := by
  unfold perimeter
  simp_rw [side_length O R hR n hn]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private theorem cross_circle_radii (O : Surcomplex.{u}) (R : SignSequence.{u})
    (θ φ : SignSequence.FiniteElement.{u}) :
    Complexify.cross (circlePoint O R θ - O) (circlePoint O R φ - O) =
      R ^ 2 * finiteSin (φ - θ) := by
  rw [finiteSin_sub]
  simp only [circlePoint, add_sub_cancel_left, Complexify.cross_def,
    mul_re, mul_im, ofReal_re, ofReal_im, finiteSin, finiteCos]
  ring

/-- Every oriented center triangle has the same positive-determinant formula. -/
theorem center_cross (O : Surcomplex.{u}) (R : SignSequence.{u}) (n k : ℕ) :
    Complexify.cross (vertex O R n k - O) (vertex O R n (k + 1) - O) =
      R ^ 2 * finiteSin (SignSequence.finiteOfReal (2 * Real.pi / n)) := by
  rw [vertex, vertex, cross_circle_radii]
  apply congrArg (fun θ : SignSequence.FiniteElement.{u} => R ^ 2 * finiteSin θ)
  rw [← map_sub]
  congr 1
  push_cast
  ring

/-- For at least three vertices, the actual sine of the one-edge central angle is positive. -/
theorem central_sin_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < finiteSin (SignSequence.finiteOfReal (2 * Real.pi / n) :
      SignSequence.FiniteElement.{u}) := by
  have hn2 : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith only [hn2]
  have hs : 0 < Real.sin (2 * Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos (mul_pos (by norm_num) Real.pi_pos) hn0)
    ((div_lt_iff₀ hn0).mpr (by nlinarith [Real.pi_pos]))
  rw [finiteSin_constant]
  simpa only [map_zero] using SignSequence.ofReal_strictMono hs

/-- All `n` center triangles have strictly positive orientation at every positive radius. -/
theorem center_cross_pos (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    0 < Complexify.cross (vertex O R n k - O) (vertex O R n (k + 1) - O) := by
  rw [center_cross]
  exact mul_pos (sq_pos_of_pos hR) (central_sin_pos n hn)

/-- Each actual center-triangle area is one half its positive determinant. -/
theorem center_triangle_area (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    triangleArea (vertex O R n k - O) (vertex O R n (k + 1) - O) =
      R ^ 2 * finiteSin (SignSequence.finiteOfReal (2 * Real.pi / n)) / 2 := by
  change |Complexify.cross (vertex O R n k - O) (vertex O R n (k + 1) - O)| / 2 = _
  rw [abs_of_pos (center_cross_pos O R hR n hn k), center_cross]

/-- Polygon area is the finite sum of the `n` actual center-triangle areas. -/
def area (O : Surcomplex.{u}) (R : SignSequence.{u}) (n : ℕ) : SignSequence.{u} :=
  ∑ k ∈ Finset.range n, triangleArea (vertex O R n k - O) (vertex O R n (k + 1) - O)

/-- Summing the positively oriented center triangles gives the source's exact area formula. -/
theorem area_eq (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (n : ℕ) (hn : 3 ≤ n) :
    area O R n = (n : SignSequence.{u}) / 2 * R ^ 2 *
      finiteSin (SignSequence.finiteOfReal (2 * Real.pi / n)) := by
  unfold area
  simp_rw [center_triangle_area O R hR n hn]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end RegularPolygon
end
end Surreal.Surcomplex
