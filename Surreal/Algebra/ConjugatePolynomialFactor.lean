import Surreal.Algebra.Complexify
import Surreal.Algebra.NonnegativePolynomialRoots

/-!
# Positive quadratic factors from conjugate roots

The nonreal-root step toward `trigonometry:lem:twosquares`.
A nonreal root of a real polynomial supplies its conjugate root and a
strictly positive real quadratic divisor. Dividing a nonnegative polynomial
by this quadratic leaves a nonnegative polynomial over the same field.
-/

namespace Surreal.Complexify

open Polynomial

noncomputable section
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The real quadratic associated with a complexified root. -/
def rootQuadratic (z : Complexify F) : F[X] := (X - C z.re) ^ 2 + C (z.im ^ 2)

/-- The quadratic is the product of the two conjugate linear factors. -/
theorem map_rootQuadratic (z : Complexify F) :
    (rootQuadratic z).map (algebraMap F (Complexify F)) =
      (X - C z) * (X - C (star z)) := by
  letI : Infinite (Complexify F) :=
    Infinite.of_injective (algebraMap F (Complexify F)) (algebraMap F (Complexify F)).injective
  apply Polynomial.funext
  intro x
  apply QuadraticAlgebra.ext <;>
    simp [rootQuadratic, pow_two] <;> ring

/-- The conjugate quadratic has degree two. -/
theorem natDegree_rootQuadratic (z : Complexify F) : (rootQuadratic z).natDegree = 2 := by
  rw [← natDegree_map_eq_of_injective (algebraMap F (Complexify F)).injective,
    map_rootQuadratic, natDegree_mul (X_sub_C_ne_zero z) (X_sub_C_ne_zero (star z))]
  simp

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The real quadratic has a literal sum-of-squares value. -/
theorem eval_rootQuadratic (z : Complexify F) (x : F) :
    (rootQuadratic z).eval x = (x - z.re) ^ 2 + z.im ^ 2 := by
  simp [rootQuadratic]

/-- A nonreal root gives a strictly positive quadratic at every real input. -/
theorem rootQuadratic_pos (z : Complexify F) (hz : z.im ≠ 0) (x : F) :
    0 < (rootQuadratic z).eval x := by
  rw [eval_rootQuadratic]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)

/-- Real coefficients are fixed by coefficientwise conjugation. -/
theorem conjugate_map_real (p : F[X]) :
    (p.map (algebraMap F (Complexify F))).map (starRingEnd (Complexify F)) =
      p.map (algebraMap F (Complexify F)) := by
  apply Polynomial.ext
  intro n
  simp only [coeff_map, starRingEnd_apply]
  apply QuadraticAlgebra.ext <;> simp

/-- Every root of a real polynomial has a conjugate root. -/
theorem isRoot_conjugate_map_real (p : F[X]) (z : Complexify F)
    (hz : (p.map (algebraMap F (Complexify F))).IsRoot z) :
    (p.map (algebraMap F (Complexify F))).IsRoot (star z) := by
  have he := eval_map_apply (p := p.map (algebraMap F (Complexify F)))
    (starRingEnd (Complexify F)) z
  rw [conjugate_map_real] at he
  change _ = star _ at he
  change (p.map (algebraMap F (Complexify F))).eval z = 0 at hz
  change (p.map (algebraMap F (Complexify F))).eval (star z) = 0
  simpa only [starRingEnd_apply, hz, star_zero] using he

/-- The conjugate quadratic divides the original real polynomial over its original field. -/
theorem rootQuadratic_dvd (p : F[X]) (z : Complexify F) (hi : z.im ≠ 0)
    (hz : (p.map (algebraMap F (Complexify F))).IsRoot z) : rootQuadratic z ∣ p := by
  have hne : z ≠ star z := by
    intro he
    have him := congrArg (fun w : Complexify F => w.im) he
    simp only [conj_im] at him
    exact hi (by linarith)
  rw [← map_dvd_map' (algebraMap F (Complexify F)), map_rootQuadratic]
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit).mul_dvd
    (dvd_iff_isRoot.mpr hz) (dvd_iff_isRoot.mpr (isRoot_conjugate_map_real p z hz))

/-- Removing the conjugate quadratic preserves nonnegativity everywhere. -/
theorem nonnegative_of_rootQuadratic_factor (q : F[X]) (z : Complexify F)
    (hi : z.im ≠ 0) (hp : ∀ x : F, 0 ≤ (rootQuadratic z * q).eval x) :
    ∀ x : F, 0 ≤ q.eval x := by
  intro x
  have he := hp x
  rw [eval_mul] at he
  exact (mul_nonneg_iff_of_pos_left (rootQuadratic_pos z hi x)).mp he

end
end Surreal.Complexify
