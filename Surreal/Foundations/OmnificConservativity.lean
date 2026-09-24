import Surreal.Foundations.OmnificDefinabilityObstructions
import Surreal.Foundations.OmnificSmallTargets

/-!
# Conservativity and its inequational boundary

The remaining counterexample in `osq:prop:conservative` and the polynomial
observation paragraph preceding it. The equational and native positive
existential equivalences are already supplied by OmnificEquationalTransfer.
The explicit sqrt(2) times omega and omega witnesses show why one inequation
breaks that transfer, and constant extraction sends both witnesses to zero.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Every small ring observation of an integer polynomial is its value at the integer constants. -/
theorem omnific_small_ringHom_polynomial_eval {σ : Type v} (p : MvPolynomial σ ℤ)
    (x : σ → OmnificInteger.{u}) {B : Type w} [Ring B] [Small.{u} B]
    (φ : OmnificInteger.{u} →+* B) :
    φ (p.eval₂ omnificIntCast x) = (p.eval (fun k => omnificConstantCoeff (x k)) : B) := by
  rw [omnific_small_ringHom_eq_constant, omnificConstantCoeff_eval]

/-- The specified infinite witnesses solve the quadratic equation and both have zero constant. -/
theorem omnific_sqrt_two_omega_solution :
    let y := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
    let x := omnificRealScale (Real.sqrt 2) y (omnificMonomial_mem_purelyInfinite 1 zero_lt_one)
    x ^ 2 = 2 * y ^ 2 ∧ y ≠ 0 ∧ omnificConstantCoeff x = 0 ∧ omnificConstantCoeff y = 0 := by
  dsimp only
  refine ⟨?_, omnificMonomial_ne_zero _ _, omnificRealScale_mem_purelyInfinite _ _ _,
    omnificMonomial_mem_purelyInfinite _ _⟩
  apply omnificToSurreal_injective
  simp only [map_pow, map_mul, map_ofNat]
  change (ofReal (Real.sqrt 2) * omegaPower 1) ^ 2 = 2 * omegaPower 1 ^ 2
  rw [mul_pow, ← map_pow, Real.sq_sqrt (by norm_num), map_ofNat]

/-- No ordinary integer solution of x squared equals twice y squared has y nonzero. -/
theorem int_no_nonzero_sqrt_two_solution : ¬ ∃ x y : ℤ, x ^ 2 = 2 * y ^ 2 ∧ y ≠ 0 := by
  rintro ⟨x, y, he, hy⟩
  have hyr : (y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hy
  have hs : (x : ℝ) ^ 2 = (Real.sqrt 2 * (y : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact_mod_cast he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hp | hn
  · exact irrational_sqrt_two.ne_rational x y ((eq_div_iff hyr).mpr hp.symm)
  · apply irrational_sqrt_two.ne_rational (-x) y
    rw [eq_div_iff hyr, Int.cast_neg]
    linarith

/-- Adding a single inequation destroys the equational conservativity of ordinary integers. -/
theorem omnific_inequational_conservativity_counterexample :
    (∃ x y : OmnificInteger.{u}, x ^ 2 = 2 * y ^ 2 ∧ y ≠ 0) ∧
      ¬ (∃ x y : ℤ, x ^ 2 = 2 * y ^ 2 ∧ y ≠ 0) := by
  refine ⟨?_, int_no_nonzero_sqrt_two_solution⟩
  exact ⟨_, _, (omnific_sqrt_two_omega_solution.{u}).1, (omnific_sqrt_two_omega_solution.{u}).2.1⟩

/-- A zero constant does not imply that the original polynomial value was zero. -/
theorem omnific_zero_constant_nonzero_polynomial_value :
    let p : MvPolynomial Unit ℤ := MvPolynomial.X ()
    let x : Unit → OmnificInteger.{u} := fun _ => omnificMonomial 1 zero_lt_one
    p.eval (fun k => omnificConstantCoeff (x k)) = 0 ∧ p.eval₂ omnificIntCast x ≠ 0 := by
  dsimp only
  rw [MvPolynomial.eval_X, MvPolynomial.eval₂_X]
  exact ⟨omnificMonomial_mem_purelyInfinite _ _, omnificMonomial_ne_zero _ _⟩

end
end Surreal.Foundations.SignSequence
