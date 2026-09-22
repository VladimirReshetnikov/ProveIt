import Surreal.Algebra.Modulus

/-!
# Finite geometry over an ordered base field

This implements the coordinate geometry in the trigonometry report:
`trigonometry:eq:dotcross`, `trigonometry:eq:gram`, the area clause of
`trigonometry:thm:heron`, and the inequality of `trigonometry:thm:ptolemy`.
Angles, circle ordering, and the cyclic equality case require further proofs.

Mathlib's Euclidean Ptolemy theorem uses a real-valued distance; here all
lengths take values in the ordered base field itself. Nonnegative square
roots suffice; real closedness is not needed for these finite identities.
-/

namespace Surreal.Complexify

section Ring

variable {F : Type*} [CommRing F]

/-- The inner product in `trigonometry:eq:dotcross`. -/
def dot (z w : Complexify F) : F := (star z * w).re

/-- The oriented determinant in `trigonometry:eq:dotcross`. -/
def cross (z w : Complexify F) : F := (star z * w).im

theorem dot_def (z w : Complexify F) : dot z w = z.re * w.re + z.im * w.im := by
  simp [dot]

theorem cross_def (z w : Complexify F) : cross z w = z.re * w.im - z.im * w.re := by
  simp [cross, sub_eq_add_neg]

theorem dot_comm (z w : Complexify F) : dot z w = dot w z := by
  simp only [dot_def]
  ring

theorem cross_swap (z w : Complexify F) : cross z w = -cross w z := by
  simp only [cross_def]
  ring

/-- Gram's identity in the report's dot/determinant notation. -/
theorem dot_sq_add_cross_sq (z w : Complexify F) :
    dot z w ^ 2 + cross z w ^ 2 = normSq z * normSq w := by
  simpa only [dot_def, cross_def, normSq] using gram_identity z.re z.im w.re w.im

theorem normSq_add (z w : Complexify F) :
    normSq (z + w) = normSq z + normSq w + 2 * dot z w := by
  simp only [normSq, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, dot_def]
  ring

/-- The finite algebra behind the cosine law. -/
theorem normSq_sub (z w : Complexify F) :
    normSq (z - w) = normSq z + normSq w - 2 * dot z w := by
  simp only [normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, dot_def]
  ring

theorem normSq_smul (r : F) (z : Complexify F) : normSq (r • z) = r ^ 2 * normSq z := by
  simp only [normSq, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- The algebraic identity used in the proof of `trigonometry:thm:ptolemy`. -/
theorem ptolemy_identity (a b c d : Complexify F) :
    (a - c) * (b - d) = (a - b) * (c - d) + (a - d) * (b - c) := by ring

end Ring

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F]

/-- Cauchy--Schwarz in the dot-product notation of the trigonometry report. -/
theorem abs_dot_le (z w : Complexify F) : |dot z w| ≤ modulus z * modulus w := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (modulus_nonneg z) (modulus_nonneg w))).mp
  simpa [dot_def, mul_pow, normSq] using cauchy_schwarz_sq z.re z.im w.re w.im

theorem modulus_smul (r : F) (z : Complexify F) : modulus (r • z) = |r| * modulus z :=
  modulus_eq_of_nonneg_sq (mul_nonneg (abs_nonneg r) (modulus_nonneg z))
    (by simp [mul_pow, normSq_smul])

/-- Triangle equality is equivalent to equality with the positive dot-product bound. -/
theorem modulus_add_eq_iff_dot (z w : Complexify F) :
    modulus (z + w) = modulus z + modulus w ↔ dot z w = modulus z * modulus w := by
  constructor
  · intro h
    have hs := congrArg (fun x : F => x ^ 2) h
    rw [modulus_sq, normSq_add, ← modulus_sq z, ← modulus_sq w] at hs
    nlinarith
  · intro h
    apply (sq_eq_sq₀ (modulus_nonneg _) (add_nonneg (modulus_nonneg z) (modulus_nonneg w))).mp
    rw [modulus_sq, normSq_add, ← modulus_sq z, ← modulus_sq w, h]
    ring

omit [HasNonnegSquareRoots F] in
theorem quotient_re (w z : Complexify F) : (w / z).re = dot z w / normSq z := by
  simp only [div_eq_mul_inv, mul_re, inv_re, inv_im, dot_def]
  ring

omit [HasNonnegSquareRoots F] in
theorem quotient_im (w z : Complexify F) : (w / z).im = cross z w / normSq z := by
  simp only [div_eq_mul_inv, mul_im, inv_re, inv_im, cross_def]
  ring

/-- The triangle-equality characterization following
`trigonometry:eq:gram`: for nonzero vectors the quotient is a positive
element of the base field. -/
theorem modulus_add_eq_iff_pos_quotient {z w : Complexify F} (hz : z ≠ 0) (hw : w ≠ 0) :
    modulus (z + w) = modulus z + modulus w ↔
      ∃ r : F, 0 < r ∧ w / z = algebraMap F (Complexify F) r := by
  constructor
  · intro h
    have hdot := (modulus_add_eq_iff_dot z w).mp h
    have hgram := dot_sq_add_cross_sq z w
    rw [hdot, mul_pow, modulus_sq, modulus_sq] at hgram
    have hcross : cross z w = 0 := sq_eq_zero_iff.mp (by linarith [hgram])
    refine ⟨dot z w / normSq z, ?_, ?_⟩
    · rw [hdot]
      exact div_pos (mul_pos (modulus_pos hz) (modulus_pos hw)) (normSq_pos hz)
    · ext
      · simp only [quotient_re, QuadraticAlgebra.algebraMap_re]
      · simp only [quotient_im, hcross, zero_div, QuadraticAlgebra.algebraMap_im]
  · rintro ⟨r, hr, hquot⟩
    have hw : w = r • z := by
      simpa only [Algebra.smul_def] using (div_eq_iff hz).mp hquot
    rw [hw]
    have hadd : z + r • z = (1 + r) • z := by rw [add_smul, one_smul]
    rw [hadd, modulus_smul, modulus_smul, abs_of_pos hr,
      abs_of_pos (by linarith : 0 < 1 + r)]
    ring

/-- The inequality clause of `trigonometry:thm:ptolemy` for arbitrary points. -/
theorem ptolemy (a b c d : Complexify F) :
    modulus (a - c) * modulus (b - d) ≤
      modulus (a - b) * modulus (c - d) + modulus (a - d) * modulus (b - c) := by
  calc
    _ = modulus ((a - c) * (b - d)) := (modulus_mul _ _).symm
    _ = modulus ((a - b) * (c - d) + (a - d) * (b - c)) := by rw [ptolemy_identity]
    _ ≤ modulus ((a - b) * (c - d)) + modulus ((a - d) * (b - c)) := modulus_add_le _ _
    _ = _ := by rw [modulus_mul, modulus_mul]

/-- The area of the triangle with vertices `0`, `z`, `w`. -/
noncomputable def triangleArea (z w : Complexify F) : F := |cross z w| / 2

omit [HasNonnegSquareRoots F] in
theorem triangleArea_nonneg (z w : Complexify F) : 0 ≤ triangleArea z w := by
  exact div_nonneg (abs_nonneg _) (by norm_num)

omit [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F] in
/-- The polynomial factorization used in `trigonometry:eq:heronfactor`. -/
theorem heron_factorization (a b c : F) :
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) =
      4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 := by ring

/-- Heron's area identity, the first clause of `trigonometry:thm:heron`.
It also holds for degenerate triangles. The remaining radius and angle clauses
of that theorem are separate obligations. -/
theorem heron (z w : Complexify F) :
    let a := modulus (z - w)
    let b := modulus w
    let c := modulus z
    let s := (a + b + c) / 2
    triangleArea z w ^ 2 = s * (s - a) * (s - b) * (s - c) := by
  dsimp only
  have hgram := dot_sq_add_cross_sq z w
  have hdist := normSq_sub z w
  have hpoly := heron_factorization (modulus (z - w)) (modulus w) (modulus z)
  rw [modulus_sq, modulus_sq, modulus_sq] at hpoly
  have hcos : normSq w + normSq z - normSq (z - w) = 2 * dot z w := by linarith
  rw [hcos] at hpoly
  have harea : triangleArea z w ^ 2 = cross z w ^ 2 / 4 := by
    simp [triangleArea, div_pow]
    ring
  rw [harea]
  nlinarith [hgram, hpoly]

end OrderedField
end Surreal.Complexify
