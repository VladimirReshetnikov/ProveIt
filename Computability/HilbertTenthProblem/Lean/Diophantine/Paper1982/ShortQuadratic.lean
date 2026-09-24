import Diophantine.Common.PolynomialDegree
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Jones 1982, §5: the explicit 58-variable quadratic system

The 36 retained variables and the 22 auxiliaries listed after (D37) give
46 quadratic equations. Their sum of squares has total degree at most four,
including the input `x` in the degree count. The index data `z`, `u`, `y`,
and the exponent `L` are fixed parameters, not polynomial variables.

The small expression type below records a syntactic degree certificate for
each displayed residual. The public residuals and sum of squares are ordinary
`MvPolynomial (Option ShortQuadraticVar) ℤ` values: `none` is the input and
`some v` is one of the 58 witnesses. The bridge modules supply witness
positivity and the equivalence with the original Pell system.
-/

namespace Jones1982

/-- The article's 36 retained witnesses, followed by its 22 auxiliaries.
`xi`, `tau`, and `eta` replace (D8), the square in (D20), and (D21). -/
inductive ShortQuadraticVar
  | B | C₁ | D | D₁ | E | F | G | H | I | K | M | N | P | R | S | T | U | Y
  | c | e | g | h | i | j | l | m | o | s | t | w | alpha | delta | gamma
  | lam | phi | epsilon
  | lamB | bSq | pellMod | AC₁ | cSq | cFourth | xi | QSq | QCube | QFourth
  | cFourthQCube | NSq | MU | PK | tau | YK | eta | AC | CSq | AE | FSq | GH
  deriving DecidableEq, Fintype

@[simp] theorem ShortQuadraticVar.card : Fintype.card ShortQuadraticVar = 58 := by
  decide

/-- Nineteen auxiliary definitions and the 27 conditions remaining after
the article's seventeen substitutions. Three auxiliaries occur directly
in (D8), (D20), and (D21), so they need no additional defining equation. -/
inductive ShortQuadraticEquation
  | lamB | bSq | pellMod | AC₁ | cSq | cFourth | QSq | QCube | QFourth
  | cFourthQCube | NSq | MU | PK | YK | AC | CSq | AE | FSq | GH
  | D2 | D3 | D4 | D5 | D6 | D8 | D9 | D10 | D16S | D16T | D17 | D18
  | D19 | D20 | D21 | D22 | D23 | D26 | D27 | D30 | D31 | D32 | D33
  | D34 | D35 | D36 | D37
  deriving DecidableEq, Fintype

@[simp] theorem ShortQuadraticEquation.card : Fintype.card ShortQuadraticEquation = 46 := by
  decide

/-- Arithmetic expressions used to certify the degree of the explicit
polynomial system. Constants may depend arbitrarily on the fixed indices. -/
inductive ShortQuadraticExpr
  | constant (a : ℤ)
  | input
  | witness (v : ShortQuadraticVar)
  | add (p q : ShortQuadraticExpr)
  | sub (p q : ShortQuadraticExpr)
  | mul (p q : ShortQuadraticExpr)
  | pow (p : ShortQuadraticExpr) (n : ℕ)

namespace ShortQuadraticExpr

instance instOfNat (n : ℕ) : OfNat ShortQuadraticExpr n := ⟨constant n⟩
instance instAdd : Add ShortQuadraticExpr := ⟨add⟩
instance instSub : Sub ShortQuadraticExpr := ⟨sub⟩
instance instMul : Mul ShortQuadraticExpr := ⟨mul⟩
instance instPow : Pow ShortQuadraticExpr ℕ := ⟨pow⟩

/-- Interpret a certificate expression as an integer multivariate polynomial. -/
noncomputable def toPolynomial : ShortQuadraticExpr →
    MvPolynomial (Option ShortQuadraticVar) ℤ
  | .constant a => MvPolynomial.C a
  | .input => MvPolynomial.X none
  | .witness v => MvPolynomial.X (some v)
  | .add p q => p.toPolynomial + q.toPolynomial
  | .sub p q => p.toPolynomial - q.toPolynomial
  | .mul p q => p.toPolynomial * q.toPolynomial
  | .pow p n => p.toPolynomial ^ n

/-- A syntactic upper bound; cancellation may lower the actual total degree. -/
def degreeBound : ShortQuadraticExpr → ℕ
  | .constant _ => 0
  | .input => 1
  | .witness _ => 1
  | .add p q => max p.degreeBound q.degreeBound
  | .sub p q => max p.degreeBound q.degreeBound
  | .mul p q => p.degreeBound + q.degreeBound
  | .pow p n => n * p.degreeBound

theorem totalDegree_toPolynomial_le (p : ShortQuadraticExpr) :
    p.toPolynomial.totalDegree ≤ p.degreeBound := by
  induction p with
  | constant a => exact (MvPolynomial.totalDegree_C a).le
  | input => exact (MvPolynomial.totalDegree_X none).le
  | witness v => exact (MvPolynomial.totalDegree_X (some v)).le
  | add p q hp hq =>
      exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max hp hq)
  | sub p q hp hq =>
      exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max hp hq)
  | mul p q hp hq =>
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
  | pow p n hp =>
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left n hp)

end ShortQuadraticExpr

namespace ShortQuadratic

abbrev Poly := MvPolynomial (Option ShortQuadraticVar) ℤ

@[simp] theorem card_polynomial_variables :
    Fintype.card (Option ShortQuadraticVar) = 59 := by
  simp

open ShortQuadraticExpr

/-- Elimination of (D1); the input has degree one. -/
def bExpr : ShortQuadraticExpr := witness .epsilon + input

/-- Elimination of (D24), using the auxiliary `MU`. -/
def AExpr : ShortQuadraticExpr := witness .MU + witness .M

/-- Elimination of (D25). -/
def CExpr : ShortQuadraticExpr :=
  2 * witness .R + 1 + witness .C₁ + witness .phi

/-- Elimination of (D7), using `lamB`. Subtraction is in the integer
polynomial ring; positivity of its evaluation is a separate implication. -/
def QExpr : ShortQuadraticExpr := 1 + witness .lamB - witness .lam

/-- The exact residuals after the article's substitutions. `z`, `u`, `y`,
and `L` enter only as coefficients. In particular `D₀` is replaced by the
signed affine expression `z * (lam + Q) - e`, not by natural subtraction. -/
def expression (z u y L : ℕ) : ShortQuadraticEquation → ShortQuadraticExpr :=
  let v := witness
  let Z := constant (z : ℤ)
  let U₀ := constant (u : ℤ)
  let Y₀ := constant (y : ℤ)
  let L₀ := constant (L : ℤ)
  let κ := constant (2 * (2 * (z : ℤ)) ^ (L + 1))
  fun
  | .lamB => v .lamB - v .lam * v .B
  | .bSq => v .bSq - bExpr ^ 2
  | .pellMod => v .pellMod - (2 * AExpr * v .B - v .B ^ 2 - 1)
  | .AC₁ => v .AC₁ - AExpr * v .C₁
  | .cSq => v .cSq - v .c ^ 2
  | .cFourth => v .cFourth - v .cSq ^ 2
  | .QSq => v .QSq - QExpr ^ 2
  | .QCube => v .QCube - QExpr * v .QSq
  | .QFourth => v .QFourth - v .QSq ^ 2
  | .cFourthQCube => v .cFourthQCube - v .cFourth * v .QCube
  | .NSq => v .NSq - v .N ^ 2
  | .MU => v .MU - v .M * v .U
  | .PK => v .PK - v .P * v .K
  | .YK => v .YK - v .Y * v .K
  | .AC => v .AC - AExpr * CExpr
  | .CSq => v .CSq - CExpr ^ 2
  | .AE => v .AE - AExpr * v .E
  | .FSq => v .FSq - v .F ^ 2
  | .GH => v .GH - v .G * v .H
  | .D2 => v .B - κ * v .bSq ^ 2
  | .D3 => v .D₁ - (QExpr + v .AC₁ - v .B * v .C₁ + v .alpha * v .pellMod)
  | .D4 => v .AC₁ ^ 2 - v .C₁ ^ 2 + 1 - v .D₁ ^ 2
  | .D5 => v .C₁ - (L₀ + v .delta * (AExpr - 1))
  | .D6 => v .c - (1 + input * v .B + v .g)
  | .D8 => v .e + 2 * Z * bExpr * v .l + 2 * Z * v .B * v .cFourth
      + v .xi - 2 * Z * QExpr
  | .D9 => v .l - (U₀ + v .t * (v .B - 2 * Z))
  | .D10 => v .e - (Y₀ + v .m * (v .B - 2 * Z))
  | .D16S => v .S - (v .g + v .l * QExpr + v .e * v .QSq
      - 4 * Z * v .cFourthQCube * (Z * (v .lam + QExpr) - v .e)
      + 2 * Z * v .lamB * (v .QCube + v .QFourth))
  | .D16T => v .T - (QExpr - 1 - (bExpr - 1) * v .l
      + (v .lamB - 2 * Z * v .lam) * (QExpr + v .QSq)
      + 2 * Z * (v .B - 2) * v .QFourth)
  | .D17 => v .N - 16 * Z * QExpr * v .QFourth
  | .D18 => v .R - (v .S * (v .NSq - v .N) + (v .T + 1) * (v .NSq - 1))
  | .D19 => v .P - 2 * v .M * v .MU
  | .D20 => v .PK ^ 2 - v .K ^ 2 + 1 - v .tau ^ 2
  | .D21 => 4 * (CExpr - v .YK) ^ 2 + v .eta - v .K ^ 2
  | .D22 => v .K - (v .R + 1 + v .h * (v .P - 1))
  | .D23 => v .M - v .R * v .Y
  | .D26 => v .U - v .NSq * v .w
  | .D27 => v .Y - v .NSq * v .s
  | .D30 => v .D - (bExpr * v .w + v .AC - 2 * CExpr
      + v .gamma * (4 * AExpr - 5))
  | .D31 => v .I - (v .D + v .o * v .F)
  | .D32 => v .D ^ 2 - (v .AC ^ 2 - v .CSq + 1)
  | .D33 => v .E - v .i * v .CSq
  | .D34 => v .FSq - (v .AE ^ 2 - v .E ^ 2 + 1)
  | .D35 => v .G - (AExpr + v .FSq * (v .FSq - AExpr))
  | .D36 => v .H - (2 * v .R + 1 + v .j * CExpr)
  | .D37 => v .I ^ 2 - (v .GH ^ 2 - v .H ^ 2 + 1)

/-- Every displayed expression has a syntactic degree bound of two. The
coefficient expressions disappear under `degreeBound`, even with symbolic
parameters. This is a finite, kernel-checked calculation for all 46 cases. -/
theorem expression_degreeBound_le_two (z u y L : ℕ) (i : ShortQuadraticEquation) :
    (expression z u y L i).degreeBound ≤ 2 := by
  cases i <;> exact Nat.le_refl 2

/-- The 46 ordinary integer multivariate polynomial residuals. Vanishing
means satisfaction of the corresponding quadratic equality; witness
positivity is intentionally supplied separately from these polynomials. -/
noncomputable def residual (z u y L : ℕ) (i : ShortQuadraticEquation) : Poly :=
  (expression z u y L i).toPolynomial

theorem residual_totalDegree_le_two (z u y L : ℕ) (i : ShortQuadraticEquation) :
    (residual z u y L i).totalDegree ≤ 2 :=
  (ShortQuadraticExpr.totalDegree_toPolynomial_le _).trans
    (expression_degreeBound_le_two z u y L i)

/-- The explicit quartic polynomial obtained by adding the squares of all
46 residuals. It uses precisely the 58-witness ambient polynomial ring. -/
noncomputable def sumSquares (z u y L : ℕ) : Poly :=
  ∑ i : ShortQuadraticEquation, residual z u y L i ^ 2

theorem sumSquares_totalDegree_le_four (z u y L : ℕ) :
    (sumSquares z u y L).totalDegree ≤ 4 :=
  Diophantine.totalDegree_sum_pow_le Finset.univ (residual z u y L) 2 2
    (fun idx _ => residual_totalDegree_le_two z u y L idx)

/-- Evaluation commutes with the displayed sum of squared residuals. -/
theorem eval_sumSquares (z u y L : ℕ) (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a (sumSquares z u y L) =
      ∑ i : ShortQuadraticEquation, (MvPolynomial.eval a (residual z u y L i)) ^ 2 := by
  simp only [sumSquares, MvPolynomial.eval_sum, MvPolynomial.eval_pow]

/-- Over the integers, the quartic vanishes exactly when all 46 quadratic
residuals vanish. The equivalence holds for arbitrary integer assignments;
the Pell-system bridge imposes witness positivity separately. -/
theorem eval_sumSquares_eq_zero_iff (z u y L : ℕ) (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a (sumSquares z u y L) = 0 ↔
      ∀ i : ShortQuadraticEquation, MvPolynomial.eval a (residual z u y L i) = 0 := by
  rw [eval_sumSquares]
  simpa only [pow_two, Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset ShortQuadraticEquation)
      (fun i => MvPolynomial.eval a (residual z u y L i)))

end ShortQuadratic

end Jones1982
