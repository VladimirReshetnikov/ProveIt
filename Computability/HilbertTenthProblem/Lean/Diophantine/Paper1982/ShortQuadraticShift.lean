import Diophantine.Paper1982.ShortQuadratic

/-!
# Jones 1982, §5: shifting the 58 witnesses and normalization

Replacing every witness by that witness plus one preserves the quadratic
degree certificates. The resulting sum of squares remains quartic in the
same 58 witnesses and the input. At the zero witness tuple, its (D9)
residual is `2*z-u`, independently of the input. Thus `2*z < u` gives the
normalization needed later without adding a witness.

The standard-coordinate module uses these identities to transfer positive
witnesses to natural witnesses and rename the variables to `Fin 59`.
-/

namespace Jones1982

namespace ShortQuadraticExpr

/-- Add one to each witness occurrence, leaving the input unchanged. -/
def shiftWitnesses : ShortQuadraticExpr → ShortQuadraticExpr
  | .constant a => .constant a
  | .input => .input
  | .witness v => .add (.witness v) (.constant 1)
  | .add p q => .add p.shiftWitnesses q.shiftWitnesses
  | .sub p q => .sub p.shiftWitnesses q.shiftWitnesses
  | .mul p q => .mul p.shiftWitnesses q.shiftWitnesses
  | .pow p n => .pow p.shiftWitnesses n

@[simp] theorem degreeBound_shiftWitnesses (p : ShortQuadraticExpr) :
    p.shiftWitnesses.degreeBound = p.degreeBound := by
  induction p <;> simp_all [shiftWitnesses, degreeBound]

end ShortQuadraticExpr

namespace ShortQuadratic

/-- The assignment induced by replacing every witness by itself plus one. -/
def shiftAssignment (a : Option ShortQuadraticVar → ℤ) : Option ShortQuadraticVar → ℤ
  | none => a none
  | some v => a (some v) + 1

end ShortQuadratic

namespace ShortQuadraticExpr

/-- The expression transform implements the actual witness substitution
at every integer evaluation, not just at the level of degree bounds. -/
theorem eval_shiftWitnesses (p : ShortQuadraticExpr)
    (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a p.shiftWitnesses.toPolynomial =
      MvPolynomial.eval (ShortQuadratic.shiftAssignment a) p.toPolynomial := by
  induction p <;>
    simp_all only [shiftWitnesses, toPolynomial, ShortQuadratic.shiftAssignment,
      MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_add,
      MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow]

end ShortQuadraticExpr

namespace ShortQuadratic

/-- The residuals after adding one to all 58 witnesses. The input and
the four fixed parameters retain their original meanings. -/
noncomputable def shiftedResidual (z u y L : ℕ) (i : ShortQuadraticEquation) : Poly :=
  (expression z u y L i).shiftWitnesses.toPolynomial

theorem shiftedResidual_totalDegree_le_two (z u y L : ℕ) (i : ShortQuadraticEquation) :
    (shiftedResidual z u y L i).totalDegree ≤ 2 := by
  refine (ShortQuadraticExpr.totalDegree_toPolynomial_le _).trans ?_
  rw [ShortQuadraticExpr.degreeBound_shiftWitnesses]
  exact expression_degreeBound_le_two z u y L i

theorem eval_shiftedResidual (z u y L : ℕ) (i : ShortQuadraticEquation)
    (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a (shiftedResidual z u y L i) =
      MvPolynomial.eval (shiftAssignment a) (residual z u y L i) :=
  ShortQuadraticExpr.eval_shiftWitnesses _ a

/-- The shifted quartic, with the same 58-witness ambient polynomial ring. -/
noncomputable def shiftedSumSquares (z u y L : ℕ) : Poly :=
  ∑ i : ShortQuadraticEquation, shiftedResidual z u y L i ^ 2

theorem shiftedSumSquares_totalDegree_le_four (z u y L : ℕ) :
    (shiftedSumSquares z u y L).totalDegree ≤ 4 :=
  Diophantine.totalDegree_sum_pow_le Finset.univ (shiftedResidual z u y L) 2 2
    (fun idx _ => shiftedResidual_totalDegree_le_two z u y L idx)

/-- Evaluation of the shifted quartic is evaluation of the original
quartic at the shifted assignment. -/
theorem eval_shiftedSumSquares (z u y L : ℕ) (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a (shiftedSumSquares z u y L) =
      MvPolynomial.eval (shiftAssignment a) (sumSquares z u y L) := by
  simp only [shiftedSumSquares, sumSquares, MvPolynomial.eval_sum,
    MvPolynomial.eval_pow, eval_shiftedResidual]

theorem eval_shiftedSumSquares_eq_zero_iff (z u y L : ℕ)
    (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a (shiftedSumSquares z u y L) = 0 ↔
      ∀ i : ShortQuadraticEquation,
        MvPolynomial.eval a (shiftedResidual z u y L i) = 0 := by
  rw [eval_shiftedSumSquares, eval_sumSquares_eq_zero_iff]
  simp only [eval_shiftedResidual]

/-- Fix the input and set all 58 polynomial witnesses to zero. -/
def zeroWitnessAssignment (x : ℤ) : Option ShortQuadraticVar → ℤ
  | none => x
  | some _ => 0

/-- With every shifted witness equal to one, (D9) has the residual
`1-(u+1*(1-2*z)) = 2*z-u`, independently of the input. -/
theorem eval_shiftedResidual_D9_zero (z u y L : ℕ) (x : ℤ) :
    MvPolynomial.eval (zeroWitnessAssignment x) (shiftedResidual z u y L .D9) =
      2 * (z : ℤ) - u := by
  rw [eval_shiftedResidual]
  change MvPolynomial.eval (shiftAssignment (zeroWitnessAssignment x))
    (MvPolynomial.X (some ShortQuadraticVar.l) -
      (MvPolynomial.C (u : ℤ) + MvPolynomial.X (some ShortQuadraticVar.t) *
        (MvPolynomial.X (some ShortQuadraticVar.B) -
          MvPolynomial.C 2 * MvPolynomial.C (z : ℤ)))) = _
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, shiftAssignment, zeroWitnessAssignment]
  ring

/-- Normalization with exactly the same 58 witnesses. The input can be
any integer; the only index inequality needed here is `2*z < u`. -/
theorem shiftedSumSquares_nonzero_at_zeroWitnesses (z u y L : ℕ)
    (hu : 2 * z < u) (x : ℤ) :
    MvPolynomial.eval (zeroWitnessAssignment x) (shiftedSumSquares z u y L) ≠ 0 := by
  intro h
  have hD9 := (eval_shiftedSumSquares_eq_zero_iff z u y L
    (zeroWitnessAssignment x)).mp h ShortQuadraticEquation.D9
  rw [eval_shiftedResidual_D9_zero] at hD9
  have huZ : 2 * (z : ℤ) < u := by exact_mod_cast hu
  omega

end ShortQuadratic

end Jones1982
