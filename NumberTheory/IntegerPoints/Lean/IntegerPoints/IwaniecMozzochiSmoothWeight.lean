import IntegerPoints.IwaniecMozzochi
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Support

/-!
# A canonical smooth weight for Iwaniec--Mozzochi

Mathlib's `Real.smoothTransition` is smooth, nonnegative, zero exactly on
`(-∞, 0]`, and positive on `(0, ∞)`.  Consequently

`canonicalSmoothWeight u v t = smoothTransition (t - u) * smoothTransition (v - t)`

is a canonical smooth bump for the interval `[u, v]`.  Its nonzero locus is
exactly `(u, v)`.  Thus, when `u < v`, its topological support is exactly the
closed interval `[u, v]`; in particular, the function vanishes at both support
endpoints rather than merely outside them.

The construction and all theorems below use only ordinary kernel-checked
Mathlib results.  There is no additional axiom, code-generation backend, or
numerical trust boundary.
-/

open Set

namespace LeanProofs.IntegerPoints

/-! ## The interval bump -/

/-- The symmetric product of two smooth transitions associated to `[u, v]`.

For `u < v`, this function is positive precisely on `(u, v)` and has
topological support `[u, v]`. -/
noncomputable def canonicalSmoothWeight (u v t : ℝ) : ℝ :=
  Real.smoothTransition (t - u) * Real.smoothTransition (v - t)

/-- Every canonical interval bump takes values in `[0, 1]`. -/
theorem canonicalSmoothWeight_mem_Icc (u v t : ℝ) :
    canonicalSmoothWeight u v t ∈ Set.Icc (0 : ℝ) 1 := by
  have hleftNonneg : 0 ≤ Real.smoothTransition (t - u) :=
    Real.smoothTransition.nonneg _
  have hrightNonneg : 0 ≤ Real.smoothTransition (v - t) :=
    Real.smoothTransition.nonneg _
  constructor
  · unfold canonicalSmoothWeight
    exact mul_nonneg hleftNonneg hrightNonneg
  · unfold canonicalSmoothWeight
    calc
      Real.smoothTransition (t - u) * Real.smoothTransition (v - t) ≤
          1 * Real.smoothTransition (v - t) :=
        mul_le_mul_of_nonneg_right
          (Real.smoothTransition.le_one _) hrightNonneg
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.smoothTransition.le_one _) zero_le_one
      _ = 1 := mul_one 1

/-- The canonical weight vanishes to the left of its left endpoint. -/
theorem canonicalSmoothWeight_eq_zero_of_le_left {u v t : ℝ} (ht : t ≤ u) :
    canonicalSmoothWeight u v t = 0 := by
  unfold canonicalSmoothWeight
  rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht), zero_mul]

/-- The canonical weight vanishes to the right of its right endpoint. -/
theorem canonicalSmoothWeight_eq_zero_of_right_le {u v t : ℝ} (ht : v ≤ t) :
    canonicalSmoothWeight u v t = 0 := by
  unfold canonicalSmoothWeight
  rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht), mul_zero]

@[simp]
theorem canonicalSmoothWeight_left_endpoint (u v : ℝ) :
    canonicalSmoothWeight u v u = 0 :=
  canonicalSmoothWeight_eq_zero_of_le_left le_rfl

@[simp]
theorem canonicalSmoothWeight_right_endpoint (u v : ℝ) :
    canonicalSmoothWeight u v v = 0 :=
  canonicalSmoothWeight_eq_zero_of_right_le le_rfl

/-- The canonical weight is strictly positive at every point of `(u, v)`. -/
theorem canonicalSmoothWeight_pos {u v t : ℝ} (hut : u < t) (htv : t < v) :
    0 < canonicalSmoothWeight u v t := by
  unfold canonicalSmoothWeight
  exact mul_pos
    (Real.smoothTransition.pos_of_pos (sub_pos.mpr hut))
    (Real.smoothTransition.pos_of_pos (sub_pos.mpr htv))

/-- The nonzero locus of the canonical weight is exactly the open interval
between its endpoints. -/
theorem canonicalSmoothWeight_ne_zero_iff {u v t : ℝ} :
    canonicalSmoothWeight u v t ≠ 0 ↔ u < t ∧ t < v := by
  constructor
  · intro ht
    constructor
    · apply lt_of_not_ge
      intro htu
      exact ht (canonicalSmoothWeight_eq_zero_of_le_left htu)
    · apply lt_of_not_ge
      intro htv
      exact ht (canonicalSmoothWeight_eq_zero_of_right_le htv)
  · rintro ⟨hut, htv⟩
    exact (canonicalSmoothWeight_pos hut htv).ne'

/-- The pointwise support (the nonzero locus) is exactly `(u, v)`. -/
theorem canonicalSmoothWeight_support (u v : ℝ) :
    Function.support (canonicalSmoothWeight u v) = Ioo u v := by
  ext t
  simp only [Function.mem_support, mem_Ioo]
  exact canonicalSmoothWeight_ne_zero_iff

/-- For a nondegenerate interval, the topological support includes both exact
endpoints and is precisely `[u, v]`. -/
theorem canonicalSmoothWeight_tsupport {u v : ℝ} (huv : u < v) :
    tsupport (canonicalSmoothWeight u v) = Icc u v := by
  change closure (Function.support (canonicalSmoothWeight u v)) = Icc u v
  rw [canonicalSmoothWeight_support, closure_Ioo huv.ne]

/-- The canonical bump satisfies the smoothness, nonnegativity, and closed
support conditions used by Iwaniec--Mozzochi. -/
theorem canonicalSmoothWeight_isSmoothWeight (u v : ℝ) :
    IsSmoothWeight (canonicalSmoothWeight u v) u v := by
  refine ⟨?_, ?_, ?_⟩
  · unfold canonicalSmoothWeight
    fun_prop
  · intro t
    unfold canonicalSmoothWeight
    exact mul_nonneg
      (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.nonneg _)
  · intro t ht
    have hinterior := canonicalSmoothWeight_ne_zero_iff.mp ht
    exact ⟨hinterior.1.le, hinterior.2.le⟩

/-- The midpoint is an explicit positive witness whenever `u < v`. -/
theorem canonicalSmoothWeight_midpoint_pos {u v : ℝ} (huv : u < v) :
    0 < canonicalSmoothWeight u v ((u + v) / 2) := by
  apply canonicalSmoothWeight_pos
  · linarith
  · linarith

/-- A canonical weight on a nondegenerate interval is not the zero function. -/
theorem canonicalSmoothWeight_ne_zero {u v : ℝ} (huv : u < v) :
    canonicalSmoothWeight u v ≠ 0 := by
  intro hzero
  have hpoint : canonicalSmoothWeight u v ((u + v) / 2) = 0 := by
    simpa using congrFun hzero ((u + v) / 2)
  exact (canonicalSmoothWeight_midpoint_pos huv).ne' hpoint

/-! ## The Section 6 weight -/

/-- A named, nonzero smooth weight for §6 of Iwaniec--Mozzochi.  Its
topological support is exactly `[4, 5]`, and it vanishes at `4` and `5`. -/
noncomputable def iwaniecMozzochiSection6Weight : ℝ → ℝ :=
  canonicalSmoothWeight 4 5

theorem iwaniecMozzochiSection6Weight_isSmoothWeight :
    IsSmoothWeight iwaniecMozzochiSection6Weight 4 5 := by
  simpa [iwaniecMozzochiSection6Weight] using
    canonicalSmoothWeight_isSmoothWeight (4 : ℝ) 5

theorem iwaniecMozzochiSection6Weight_tsupport :
    tsupport iwaniecMozzochiSection6Weight = Icc 4 5 := by
  simpa [iwaniecMozzochiSection6Weight] using
    canonicalSmoothWeight_tsupport (u := (4 : ℝ)) (v := 5) (by norm_num)

/-- The midpoint `9 / 2` is an explicit positive witness for the Section 6
weight. -/
theorem iwaniecMozzochiSection6Weight_pos :
    0 < iwaniecMozzochiSection6Weight ((9 : ℝ) / 2) := by
  unfold iwaniecMozzochiSection6Weight
  apply canonicalSmoothWeight_pos <;> norm_num

theorem iwaniecMozzochiSection6Weight_ne_zero :
    iwaniecMozzochiSection6Weight ≠ 0 := by
  simpa [iwaniecMozzochiSection6Weight] using
    canonicalSmoothWeight_ne_zero (u := (4 : ℝ)) (v := 5) (by norm_num)

/-- The Section 6 smooth-weight hypotheses are jointly inhabited by a concrete
ordinary Mathlib function. -/
theorem exists_iwaniecMozzochiSection6Weight :
    ∃ ρ : ℝ → ℝ, IsSmoothWeight ρ 4 5 ∧ ρ ≠ 0 :=
  ⟨iwaniecMozzochiSection6Weight,
    iwaniecMozzochiSection6Weight_isSmoothWeight,
    iwaniecMozzochiSection6Weight_ne_zero⟩

end LeanProofs.IntegerPoints
