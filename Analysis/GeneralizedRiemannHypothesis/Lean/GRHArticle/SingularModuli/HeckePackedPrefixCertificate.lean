import GRHArticle.SingularModuli.HeckePackedPolynomialArithmetic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Checking a polynomial prefix with one exact residue

If the evaluation at a sufficiently large integer base is divisible by a
power of the base, the corresponding low coefficients vanish. Bounding
coefficients by the absolute-value polynomial makes this a finite check
that uses packed integer arithmetic without decoding intermediate products.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- Polynomial operations used by the arithmetic checks. Leaves have
coefficients listed in increasing index order. -/
inductive IntegerPolynomialExpression where
  | coefficients (cs : List ℤ)
  | add (a b : IntegerPolynomialExpression)
  | sub (a b : IntegerPolynomialExpression)
  | mul (a b : IntegerPolynomialExpression)
  | pow (a : IntegerPolynomialExpression) (n : ℕ)

namespace IntegerPolynomialExpression

/-- The mathematical polynomial represented by an expression. -/
noncomputable def polynomial : IntegerPolynomialExpression → Polynomial ℤ
  | .coefficients cs => coefficientListPolynomial cs
  | .add a b => a.polynomial + b.polynomial
  | .sub a b => a.polynomial - b.polynomial
  | .mul a b => a.polynomial * b.polynomial
  | .pow a n => a.polynomial ^ n

private noncomputable def absolutePolynomial : IntegerPolynomialExpression → Polynomial ℕ
  | .coefficients cs => coefficientListPolynomial (cs.map Int.natAbs)
  | .add a b | .sub a b => a.absolutePolynomial + b.absolutePolynomial
  | .mul a b => a.absolutePolynomial * b.absolutePolynomial
  | .pow a n => a.absolutePolynomial ^ n

/-- Upper bound on the absolute value of every coefficient. -/
def magnitudeBound : IntegerPolynomialExpression → ℕ
  | .coefficients cs => (cs.map Int.natAbs).sum
  | .add a b | .sub a b => a.magnitudeBound + b.magnitudeBound
  | .mul a b => a.magnitudeBound * b.magnitudeBound
  | .pow a n => a.magnitudeBound ^ n

private theorem eval_one_coefficientListPolynomial (cs : List ℕ) :
    (coefficientListPolynomial cs).eval 1 = cs.sum := by
  induction cs with
  | nil => simp [coefficientListPolynomial]
  | cons c cs h => simp [coefficientListPolynomial, h]

private theorem absolutePolynomial_eval_one (e : IntegerPolynomialExpression) :
    e.absolutePolynomial.eval 1 = e.magnitudeBound := by
  induction e <;> simp [absolutePolynomial, magnitudeBound, *, eval_one_coefficientListPolynomial]

private theorem coeff_abs_le_mul {P Q : Polynomial ℤ} {P' Q' : Polynomial ℕ}
    (hP : ∀ k, (P.coeff k).natAbs ≤ P'.coeff k)
    (hQ : ∀ k, (Q.coeff k).natAbs ≤ Q'.coeff k) (n : ℕ) :
    ((P * Q).coeff n).natAbs ≤ (P' * Q').coeff n := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hP _) (hQ _)

private theorem coeff_abs_le_absolutePolynomial (e : IntegerPolynomialExpression) (i : ℕ) :
    (e.polynomial.coeff i).natAbs ≤ e.absolutePolynomial.coeff i := by
  induction e generalizing i with
  | coefficients cs =>
    simp only [polynomial, absolutePolynomial, coeff_coefficientListPolynomial,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : cs[i]? <;> simp
  | add a b ha hb =>
    simp only [polynomial, absolutePolynomial, coeff_add]
    exact (Int.natAbs_add_le ..).trans (Nat.add_le_add (ha i) (hb i))
  | sub a b ha hb =>
    simp only [polynomial, absolutePolynomial, coeff_sub, coeff_add]
    exact (Int.natAbs_sub_le ..).trans (Nat.add_le_add (ha i) (hb i))
  | mul a b ha hb => exact coeff_abs_le_mul ha hb i
  | pow a n ha =>
    simp only [polynomial, absolutePolynomial]
    induction n generalizing i with
    | zero => by_cases h : i = 0 <;> simp [coeff_one, h]
    | succ k hk =>
      simp only [pow_succ]
      exact coeff_abs_le_mul hk ha i

private theorem coeff_le_eval_one (P : Polynomial ℕ) (k : ℕ) : P.coeff k ≤ P.eval 1 := by
  by_cases hk : k ≤ P.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    simp only [one_pow, mul_one]
    exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (P.coeff i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk)]

theorem natAbs_coeff_le_magnitudeBound (e : IntegerPolynomialExpression) (n : ℕ) :
    (e.polynomial.coeff n).natAbs ≤ e.magnitudeBound := by
  rw [← absolutePolynomial_eval_one]
  exact (coeff_abs_le_absolutePolynomial e n).trans (coeff_le_eval_one _ n)

private def packSignedDigits (w : ℕ) (cs : List ℤ) : ℤ :=
  (packPolynomialDigits w (cs.map Int.toNat) : ℤ) -
    (packPolynomialDigits w (cs.map fun a ↦ (-a).toNat) : ℤ)

private theorem packSignedDigits_eq_eval (w : ℕ) (cs : List ℤ) :
    packSignedDigits w cs = (coefficientListPolynomial cs).eval (2^w) := by
  induction cs with
  | nil => simp [packSignedDigits, packPolynomialDigits, coefficientListPolynomial]
  | cons c cs ih =>
    simp only [packSignedDigits, List.map_cons, packPolynomialDigits, Nat.shiftLeft_eq,
      Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      coefficientListPolynomial, eval_add, eval_mul, eval_X, eval_C] at *
    have htwo : ((2 : ℕ) : ℤ) = 2 := rfl
    rw [htwo]
    linear_combination ((2 : ℤ)^w) * ih + Int.toNat_sub_toNat_neg c

/-- Evaluate the expression on a binary base using exact packed inputs. -/
def packedEval (w : ℕ) : IntegerPolynomialExpression → ℤ
  | .coefficients cs => packSignedDigits w cs
  | .add a b => a.packedEval w + b.packedEval w
  | .sub a b => a.packedEval w - b.packedEval w
  | .mul a b => a.packedEval w * b.packedEval w
  | .pow a n => a.packedEval w ^ n

theorem packedEval_eq_eval (e : IntegerPolynomialExpression) (w : ℕ) :
    e.packedEval w = e.polynomial.eval (2^w) := by
  induction e <;> simp [packedEval, polynomial, *, packSignedDigits_eq_eval]

private theorem eval_eq_coeff_zero_add_mul_divX (b : ℤ) (P : Polynomial ℤ) :
    P.eval b = P.coeff 0 + b * P.divX.eval b := by
  have h := congrArg (Polynomial.eval b) P.X_mul_divX_add
  simpa only [eval_add, eval_mul, eval_X, eval_C, add_comm] using h.symm

private theorem coeff_zero_prefix_of_pow_dvd_eval (b : ℤ) (hb : b ≠ 0) (P : Polynomial ℤ) (n : ℕ)
    (hbound : ∀ i < n, (P.coeff i).natAbs < b.natAbs) (h : b^n ∣ P.eval b) :
    ∀ i < n, P.coeff i = 0 := by
  induction n generalizing P with
  | zero => intro i hi; omega
  | succ n ih =>
    have hbP : b ∣ P.eval b := (dvd_pow_self b (Nat.succ_ne_zero _)).trans h
    rw [eval_eq_coeff_zero_add_mul_divX] at hbP h
    have h0 : P.coeff 0 = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
      ((dvd_add_left (dvd_mul_right b (P.divX.eval b))).mp hbP) (hbound 0 (Nat.succ_pos _))
    rw [h0, zero_add, pow_succ'] at h
    have hd : b^n ∣ P.divX.eval b := Int.dvd_of_mul_dvd_mul_left hb h
    have hnext (i : ℕ) (hi : i < n) : (P.divX.coeff i).natAbs < b.natAbs := by
      rw [coeff_divX]
      exact hbound (i+1) (Nat.succ_lt_succ hi)
    intro i hi
    cases i with
    | zero => exact h0
    | succ i => rw [← coeff_divX]; exact ih P.divX hnext hd i (Nat.lt_of_succ_lt_succ hi)

/-- A divisibility check with a base larger than every coefficient. -/
def checkZeroPrefix (e : IntegerPolynomialExpression) (n : ℕ) : Prop :=
  let w := e.magnitudeBound.log2 + 1
  e.packedEval w % ((1 <<< (w*n) : ℕ) : ℤ) = 0

instance (e : IntegerPolynomialExpression) (n : ℕ) : Decidable (e.checkZeroPrefix n) := by
  unfold checkZeroPrefix
  infer_instance

/-- A passed finite check proves all the requested coefficients are zero. -/
theorem coeff_eq_zero_of_checkZeroPrefix (e : IntegerPolynomialExpression) (n : ℕ)
    (h : e.checkZeroPrefix n) (i : ℕ) (hi : i < n) : e.polynomial.coeff i = 0 := by
  let w := e.magnitudeBound.log2+1
  have hz : ((2:ℤ)^w)^n ∣ e.polynomial.eval (2^w) := by
    apply Int.dvd_of_emod_eq_zero
    change e.packedEval w % ((1 <<< (w*n) : ℕ) : ℤ) = 0 at h
    rw [packedEval_eq_eval, Nat.one_shiftLeft, pow_mul, Int.natCast_pow, Int.natCast_pow] at h
    exact h
  apply coeff_zero_prefix_of_pow_dvd_eval _ (pow_ne_zero _ (by decide)) _ n _ hz i hi
  intro k _
  rw [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 by decide]
  exact (natAbs_coeff_le_magnitudeBound e k).trans_lt Nat.lt_log2_self

end IntegerPolynomialExpression

end GRHArticle.SingularModuli
