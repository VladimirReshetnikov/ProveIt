import Surreal.Algebra.FormalCoordinateChange
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Diagonal formal coordinates for the coupled quadratic germ

The linear change `X=H+J`, `Y=H-J` is a formal algebra automorphism.
It identifies the translated two-equation ideal in `trigonometry:sec:coupled`
with the separated ideal `(X²+2pX, Y²+2qY)` where `p=x+y`, `q=x-y`.
-/

namespace Surreal.FormalCoupled

open MvPowerSeries

noncomputable section

open Classical

variable {K : Type*} [Field K] [CharZero K]

abbrev Series := MvPowerSeries (Fin 2) K

/-- The two sum-and-difference coordinate series. -/
def forward (i : Fin 2) : Series (K := K) := if i = 0 then X 0 + X 1 else X 0 - X 1

/-- The inverse coordinate series. -/
def backward (i : Fin 2) : Series (K := K) := C (1 / 2 : K) * forward i

omit [CharZero K] in
theorem hasSubst_forward : HasSubst (forward (K := K)) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [forward]

omit [CharZero K] in
theorem hasSubst_backward : HasSubst (backward (K := K)) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [backward, forward]

private theorem two_mul_half : (2 : Series (K := K)) * C (1 / 2 : K) = 1 := by
  rw [← map_ofNat C 2, ← map_mul]
  norm_num

theorem subst_backward_forward (i : Fin 2) :
    subst (backward (K := K)) (forward (K := K) i) = X i := by
  have hc := two_mul_half (K := K)
  simp only [one_div] at hc
  fin_cases i
  · simp [forward, backward, subst_add hasSubst_backward, subst_X hasSubst_backward]
    linear_combination (X (0 : Fin 2) : Series (K := K)) * hc
  · simp [forward, backward, subst_sub hasSubst_backward, subst_X hasSubst_backward]
    linear_combination (X (1 : Fin 2) : Series (K := K)) * hc

theorem subst_forward_backward (i : Fin 2) :
    subst (forward (K := K)) (backward (K := K) i) = X i := by
  have hc := two_mul_half (K := K)
  simp only [one_div] at hc
  fin_cases i
  · simp [backward, forward, subst_mul hasSubst_forward,
      subst_add hasSubst_forward, subst_X hasSubst_forward]
    linear_combination (X (0 : Fin 2) : Series (K := K)) * hc
  · simp [backward, forward, subst_mul hasSubst_forward,
      subst_sub hasSubst_forward, subst_X hasSubst_forward]
    linear_combination (X (1 : Fin 2) : Series (K := K)) * hc

/-- The linear diagonalization is an equivalence of the entire formal series ring. -/
def diagonalChange : Series (K := K) ≃ₐ[K] Series (K := K) :=
  FormalCoordinate.ofFamilies forward backward hasSubst_forward hasSubst_backward
    subst_forward_backward subst_backward_forward

@[simp] theorem diagonalChange_X (i : Fin 2) : diagonalChange (X i : Series (K := K)) = forward i :=
  substAlgHom_X hasSubst_forward i

@[simp] theorem diagonalChange_C (k : K) : diagonalChange (C k) = C k :=
  diagonalChange.commutes k

/-- The first translated polynomial relation at a root with sine coordinates `x,y`. -/
def first (x y : K) : Series (K := K) :=
  X 0 ^ 2 + X 1 ^ 2 + 2 * C x * X 0 + 2 * C y * X 1

/-- The second translated polynomial relation. -/
def second (x y : K) : Series (K := K) := X 0 * X 1 + C x * X 1 + C y * X 0

/-- A diagonal quadratic translated to its selected root. -/
def diagonal (p : K) (i : Fin 2) : Series (K := K) := X i ^ 2 + 2 * C p * X i

theorem diagonalChange_first (x y : K) :
    diagonalChange (diagonal (x + y) 0) = first x y + 2 * second x y := by
  simp only [diagonal, map_add, map_pow, map_mul, map_ofNat, diagonalChange_X,
    diagonalChange_C, forward, ↓reduceIte, first, second]
  ring

theorem diagonalChange_second (x y : K) :
    diagonalChange (diagonal (x - y) 1) = first x y - 2 * second x y := by
  simp only [diagonal, map_add, map_pow, map_mul, map_ofNat, diagonalChange_X,
    diagonalChange_C, forward, one_ne_zero, ↓reduceIte, first, second]
  rw [map_sub]
  ring

/-- The two invertible linear combinations generate exactly the original ideal. -/
theorem span_add_sub (f g : Series (K := K)) :
    Ideal.span {f + 2 * g, f - 2 * g} = Ideal.span {f, g} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 2, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨1, -2, by ring⟩
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · subst z
      apply Ideal.mem_span_pair.mpr
      refine ⟨C (1 / 2 : K), C (1 / 2 : K), ?_⟩
      linear_combination f * two_mul_half (K := K)
    · subst z
      have hc : (4 : Series (K := K)) * C (1 / 4 : K) = 1 := by
        rw [← map_ofNat C 4, ← map_mul]
        norm_num
      apply Ideal.mem_span_pair.mpr
      refine ⟨C (1 / 4 : K), -C (1 / 4 : K), ?_⟩
      linear_combination g * hc

/-- The diagonal ideal represents the translated polynomial system exactly. -/
theorem map_diagonalIdeal (x y : K) :
    (Ideal.span {diagonal (x + y) 0, diagonal (x - y) 1}).map diagonalChange.toRingHom =
      Ideal.span {first x y, second x y} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {diagonalChange (diagonal (x + y) 0),
    diagonalChange (diagonal (x - y) 1)} = _
  rw [diagonalChange_first, diagonalChange_second, span_add_sub]

/-- The induced local formal quotient equivalence preserves all nilpotent structure. -/
def diagonalQuotientEquiv (x y : K) :
    (Series (K := K) ⧸ Ideal.span {diagonal (x + y) 0, diagonal (x - y) 1}) ≃ₐ[K]
      Series (K := K) ⧸ Ideal.span {first x y, second x y} :=
  Ideal.quotientEquivAlg _ _ diagonalChange (map_diagonalIdeal x y).symm

/-- A nonzero translated root contributes a unit linear factor. -/
theorem isUnit_linear_factor (p : K) (hp : p ≠ 0) (i : Fin 2) :
    IsUnit (X i + C (2 * p) : Series (K := K)) := by
  rw [isUnit_iff_constantCoeff]
  simpa using (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : K) ≠ 0) hp))

/-- The order retained by the translated diagonal relation is one or two. -/
def localExponent (p : K) : ℕ := if p = 0 then 2 else 1

/-- Removing a unit factor preserves the entire principal ideal. -/
theorem span_diagonal (p : K) (i : Fin 2) :
    Ideal.span {diagonal p i} = Ideal.span {(X i : Series (K := K)) ^ localExponent p} := by
  by_cases hp : p = 0
  · subst p
    simp [diagonal, localExponent]
  · have hf : diagonal p i = X i * (X i + C (2 * p)) := by
      simp only [diagonal, map_mul, map_ofNat]
      ring
    rw [hf, Ideal.span_singleton_mul_right_unit (isUnit_linear_factor p hp i)]
    simp [localExponent, hp]

/-- Both translated diagonal relations reduce to pure powers, without taking radicals. -/
theorem diagonalIdeal_eq_powers (p q : K) :
    Ideal.span {diagonal p 0, diagonal q 1} =
      Ideal.span {(X 0 : Series (K := K)) ^ localExponent p, X 1 ^ localExponent q} := by
  rw [Ideal.span_insert, Ideal.span_insert, span_diagonal, span_diagonal]

/-- The truncated formal algebra is isomorphic to the original translated quadratic germ. -/
def truncatedQuotientEquiv (x y : K) :
    (Series (K := K) ⧸ Ideal.span {(X 0 : Series (K := K)) ^ localExponent (x + y),
      X 1 ^ localExponent (x - y)}) ≃ₐ[K]
      Series (K := K) ⧸ Ideal.span {first x y, second x y} :=
  (Ideal.quotientEquivAlgOfEq K (diagonalIdeal_eq_powers (x + y) (x - y)).symm).trans
    (diagonalQuotientEquiv x y)

end
end Surreal.FormalCoupled
