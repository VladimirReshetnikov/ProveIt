import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Translation to a monic depressed polynomial

This is the finite change of coordinates preceding the odd-degree-root
argument in Conway, *On Numbers and Games*, Chapter 3, Theorem 25, relevant
to `found:sub:realclosed` in the foundations article. Translating a monic
degree-`n` polynomial by minus its next-to-leading coefficient divided by `n`
removes that coefficient. Degree, monicity, and roots are transported
explicitly. Characteristic zero ensures the positive degree is invertible.

No existence of a polynomial root or real-closedness assertion is assumed.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

/-- The coefficient immediately below the leading degree after translation.
This identity itself holds without a characteristic assumption. -/
theorem coeff_taylor_pred_natDegree {R : Type*} [CommSemiring R]
    (P : R[X]) (hpos : 0 < P.natDegree) (r : R) :
    (taylor r P).coeff (P.natDegree - 1) =
      (P.natDegree : R) * P.leadingCoeff * r + P.coeff (P.natDegree - 1) := by
  have hbound : (hasseDeriv (P.natDegree - 1) P).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le P _).trans (by omega)
  have hindex : 1 + (P.natDegree - 1) = P.natDegree := by omega
  rw [taylor_coeff, eq_X_add_C_of_natDegree_le_one hbound]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
    hindex, zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.choose_symm (show 1 ≤ P.natDegree by omega), Nat.choose_one_right,
    coeff_natDegree]

section Field

variable {K : Type*} [Field K]

/-- Divide a polynomial by its leading coefficient. Nonzero inputs become
monic, without changing degree or roots. -/
def monicNormalize (P : K[X]) : K[X] := P * C P.leadingCoeff⁻¹

theorem monic_monicNormalize {P : K[X]} (hP : P ≠ 0) : (monicNormalize P).Monic :=
  monic_mul_leadingCoeff_inv hP

theorem natDegree_monicNormalize {P : K[X]} (hP : P ≠ 0) :
    (monicNormalize P).natDegree = P.natDegree := by
  rw [monicNormalize, natDegree_mul hP
    (C_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hP))), natDegree_C, add_zero]

@[simp] theorem eval_monicNormalize (P : K[X]) (x : K) :
    (monicNormalize P).eval x = P.eval x / P.leadingCoeff := by
  simp only [monicNormalize, eval_mul, eval_C, div_eq_mul_inv]

theorem isRoot_monicNormalize_iff {P : K[X]} (hP : P ≠ 0) (x : K) :
    (monicNormalize P).IsRoot x ↔ P.IsRoot x := by
  simp only [IsRoot, eval_monicNormalize, div_eq_zero_iff,
    leadingCoeff_ne_zero.mpr hP, or_false]

/-- The amount subtracted from the variable to remove the next coefficient
of a positive-degree monic polynomial. -/
def depressionShift (P : K[X]) : K :=
  P.coeff (P.natDegree - 1) / (P.natDegree : K)

/-- Translation by minus the next-to-leading coefficient divided by the degree.
The definition is total, while its depressed-coefficient property requires
positive degree and monicity. -/
def depress (P : K[X]) : K[X] := taylor (-depressionShift P) P

theorem depress_eq_comp (P : K[X]) :
    depress P = P.comp (X - C (depressionShift P)) := by
  simp only [depress, taylor_apply, map_neg, sub_eq_add_neg]

@[simp] theorem natDegree_depress (P : K[X]) : (depress P).natDegree = P.natDegree :=
  natDegree_taylor _ _

@[simp] theorem degree_depress (P : K[X]) : (depress P).degree = P.degree :=
  degree_taylor _ _

@[simp] theorem leadingCoeff_depress (P : K[X]) :
    (depress P).leadingCoeff = P.leadingCoeff := leadingCoeff_taylor _ _

theorem monic_depress {P : K[X]} (hP : P.Monic) : (depress P).Monic := by
  simpa only [Monic, leadingCoeff_depress] using hP

@[simp] theorem eval_depress (P : K[X]) (x : K) :
    (depress P).eval x = P.eval (x - depressionShift P) := by
  simpa only [depress, sub_eq_add_neg] using taylor_eval (-depressionShift P) P x

/-- Translating back recovers the original polynomial exactly. -/
theorem taylor_depressionShift_depress (P : K[X]) :
    taylor (depressionShift P) (depress P) = P := by
  rw [depress, taylor_taylor, add_neg_cancel, taylor_zero]

theorem isRoot_depress_iff (P : K[X]) (x : K) :
    (depress P).IsRoot x ↔ P.IsRoot (x - depressionShift P) := by
  simp only [IsRoot, eval_depress]

theorem isRoot_of_isRoot_depress {P : K[X]} {x : K}
    (hx : (depress P).IsRoot x) : P.IsRoot (x - depressionShift P) :=
  (isRoot_depress_iff P x).mp hx

theorem exists_root_depress_iff (P : K[X]) :
    (∃ x : K, (depress P).IsRoot x) ↔ ∃ x : K, P.IsRoot x := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x - depressionShift P, isRoot_of_isRoot_depress hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨x + depressionShift P, (isRoot_depress_iff P _).mpr ?_⟩
    simpa only [add_sub_cancel_right] using hx

/-- Explicit root pullback after both leading-coefficient normalization and
translation to depressed form. -/
theorem isRoot_of_isRoot_depress_monicNormalize {P : K[X]} (hP : P ≠ 0) {x : K}
    (hx : (depress (monicNormalize P)).IsRoot x) :
    P.IsRoot (x - depressionShift (monicNormalize P)) :=
  (isRoot_monicNormalize_iff hP _).mp (isRoot_of_isRoot_depress hx)

variable [CharZero K]

/-- The translated monic polynomial is depressed. The positive-degree guard
also excludes the constant-polynomial convention for `natDegree - 1`. -/
theorem coeff_depress_pred_eq_zero {P : K[X]} (hP : P.Monic)
    (hpos : 0 < P.natDegree) : (depress P).coeff (P.natDegree - 1) = 0 := by
  rw [depress, coeff_taylor_pred_natDegree P hpos, hP.leadingCoeff, mul_one]
  have hn : (P.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  simp only [depressionShift, mul_neg, mul_div_cancel₀ _ hn, neg_add_cancel]

theorem nextCoeff_depress_eq_zero {P : K[X]} (hP : P.Monic) :
    (depress P).nextCoeff = 0 := by
  by_cases hpos : 0 < P.natDegree
  · rw [nextCoeff_of_natDegree_pos (by simpa using hpos), natDegree_depress]
    exact coeff_depress_pred_eq_zero hP hpos
  · have hn : P.natDegree = 0 := by omega
    simp only [nextCoeff, natDegree_depress, hn, ite_true]

/-- Every nonzero positive-degree polynomial reduces to a monic depressed
polynomial of the same degree, with equivalent root existence. -/
theorem exists_monic_depressed {P : K[X]} (hP : P ≠ 0) (hpos : 0 < P.natDegree) :
    ∃ D : K[X], D.Monic ∧ D.natDegree = P.natDegree ∧
      D.coeff (D.natDegree - 1) = 0 ∧
      ((∃ x : K, D.IsRoot x) ↔ ∃ x : K, P.IsRoot x) := by
  refine ⟨depress (monicNormalize P), monic_depress (monic_monicNormalize hP), ?_, ?_, ?_⟩
  · rw [natDegree_depress, natDegree_monicNormalize hP]
  · rw [natDegree_depress]
    exact coeff_depress_pred_eq_zero (monic_monicNormalize hP)
      (by simpa only [natDegree_monicNormalize hP] using hpos)
  · rw [exists_root_depress_iff]
    simp only [isRoot_monicNormalize_iff hP]

end Field

end

end Surreal.FinitePolynomial
