import GRHArticle.SingularModuli.HeckePackedPrefixCertificate
import GRHArticle.SingularModuli.HeckeSeriesPrefixArithmetic

/-!
# Series correctness of the packed polynomial checks

Only low coefficients are needed. Expressions built from certified
prefixes agree with the corresponding operations on the full series.
-/

namespace GRHArticle.SingularModuli

open scoped PowerSeries

namespace IntegerPolynomialExpression

/-- The expression gives the first `N` coefficients of a formal series. -/
def AgreesWith (e : IntegerPolynomialExpression) (N : ℕ) (F : ℤ⟦X⟧) : Prop :=
  ∀ i : Fin N, e.polynomial.coeff i = F.coeff i

variable {N : ℕ} {a b : IntegerPolynomialExpression} {F G : ℤ⟦X⟧}

theorem coefficients_spec {l : List ℤ} (h : SeriesPrefix N l F) :
    (coefficients l).AgreesWith N F := by
  intro i
  rw [polynomial, coeff_coefficientListPolynomial, h i]

theorem constant_spec (c : ℤ) :
    (coefficients [c]).AgreesWith N (PowerSeries.C c) := by
  intro i
  simp only [polynomial, coefficientListPolynomial, mul_zero, add_zero,
    Polynomial.coeff_C, PowerSeries.coeff_C]

theorem X_spec : (coefficients [0,1]).AgreesWith N (PowerSeries.X : ℤ⟦X⟧) := by
  intro i
  simp only [polynomial, coefficientListPolynomial, mul_zero, add_zero, map_zero, map_one,
    zero_add, mul_one, Polynomial.coeff_X, PowerSeries.coeff_X]
  by_cases h : (i : ℕ) = 1
  · simp [h]
  · simp [h, Ne.symm h]

theorem add_spec (ha : a.AgreesWith N F) (hb : b.AgreesWith N G) :
    (add a b).AgreesWith N (F+G) := by
  intro i
  rw [polynomial, Polynomial.coeff_add, ha i, hb i, map_add]

theorem sub_spec (ha : a.AgreesWith N F) (hb : b.AgreesWith N G) :
    (sub a b).AgreesWith N (F-G) := by
  intro i
  rw [polynomial, Polynomial.coeff_sub, ha i, hb i, map_sub]

theorem mul_spec (ha : a.AgreesWith N F) (hb : b.AgreesWith N G) :
    (mul a b).AgreesWith N (F*G) := by
  intro i
  rw [polynomial, Polynomial.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hsum := Finset.mem_antidiagonal.mp hk
  rw [ha ⟨k.1, by have := i.isLt; omega⟩, hb ⟨k.2, by have := i.isLt; omega⟩]

theorem pow_spec (ha : a.AgreesWith N F) (k : ℕ) : (pow a k).AgreesWith N (F^k) := by
  induction k with
  | zero =>
    intro i
    simp only [polynomial, _root_.pow_zero, Polynomial.coeff_one, PowerSeries.coeff_one]
  | succ k ih =>
    simpa only [AgreesWith, polynomial, pow_succ] using mul_spec ih ha

/-- Sum expressions without expanding any intermediate coefficient lists. -/
def sum : List IntegerPolynomialExpression → IntegerPolynomialExpression
  | [] => .coefficients []
  | a :: as => .add a (sum as)

private theorem coeff_sum (l : List IntegerPolynomialExpression) (i : ℕ) :
    (sum l).polynomial.coeff i = (l.map fun e ↦ e.polynomial.coeff i).sum := by
  induction l with
  | nil => simp [sum, polynomial, coefficientListPolynomial]
  | cons e l h => simp only [sum, polynomial, Polynomial.coeff_add, h, List.map_cons, List.sum_cons]

theorem sum_spec {n : ℕ} (e : Fin n → IntegerPolynomialExpression) (F : Fin n → ℤ⟦X⟧)
    (h : ∀ i, (e i).AgreesWith N (F i)) :
    (sum (List.ofFn e)).AgreesWith N (∑ i, F i) := by
  intro i
  rw [coeff_sum, List.map_ofFn, List.sum_ofFn, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ h j i

theorem series_coeff_eq_zero_of_check {e : IntegerPolynomialExpression} (h : e.checkZeroPrefix N)
    (ha : e.AgreesWith N F) (i : Fin N) : F.coeff i = 0 :=
  (ha i).symm.trans (coeff_eq_zero_of_checkZeroPrefix e N h i i.isLt)

theorem series_prefix_eq_of_check {a b : IntegerPolynomialExpression} (h : (sub a b).checkZeroPrefix N)
    (ha : a.AgreesWith N F) (hb : b.AgreesWith N G) (i : Fin N) :
    F.coeff i = G.coeff i := by
  have hz := series_coeff_eq_zero_of_check h (sub_spec ha hb) i
  rwa [map_sub, sub_eq_zero] at hz

end IntegerPolynomialExpression

end GRHArticle.SingularModuli
