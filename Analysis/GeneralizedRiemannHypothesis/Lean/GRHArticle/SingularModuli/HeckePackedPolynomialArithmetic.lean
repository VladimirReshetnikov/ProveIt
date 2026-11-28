import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Exact packed polynomial multiplication

Encoding nonnegative coefficients as binary digits wider than their
possible convolution realizes truncated multiplication as one natural
number multiplication and exact digit extraction.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- The polynomial with coefficients listed in increasing degree order. -/
noncomputable def coefficientListPolynomial {R : Type*} [Semiring R] : List R → Polynomial R
  | [] => 0
  | a :: as => C a + X * coefficientListPolynomial as

theorem coeff_coefficientListPolynomial {R : Type*} [Semiring R] (l : List R) (n : ℕ) :
    (coefficientListPolynomial l).coeff n = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [coefficientListPolynomial]
  | cons a as ih =>
    cases n with
    | zero => simp [coefficientListPolynomial]
    | succ n =>
      simp [coefficientListPolynomial, Polynomial.coeff_X_mul, ih]

/-- Pack a low-degree-first list in digits of bit width `w`. -/
def packPolynomialDigits (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => a + (packPolynomialDigits w as <<< w)

private theorem packPolynomialDigits_eq_eval (w : ℕ) (l : List ℕ) :
    packPolynomialDigits w l = (coefficientListPolynomial l).eval (2^w) := by
  induction l with
  | nil => simp [packPolynomialDigits, coefficientListPolynomial]
  | cons a as ih =>
    simp [packPolynomialDigits, coefficientListPolynomial, Nat.shiftLeft_eq, ih, mul_comm]

private theorem eval_one_coefficientListPolynomial (l : List ℕ) :
    (coefficientListPolynomial l).eval 1 = l.sum := by
  induction l with
  | nil => simp [coefficientListPolynomial]
  | cons a as ih => simp [coefficientListPolynomial, ih]

private theorem coeff_le_eval_one (P : Polynomial ℕ) (k : ℕ) : P.coeff k ≤ P.eval 1 := by
  by_cases hk : k ≤ P.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    simp only [one_pow, mul_one]
    exact Finset.single_le_sum (fun i hi ↦ Nat.zero_le (P.coeff i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk)]

private theorem eval_eq_coeff_zero_add_mul_divX (b : ℕ) (P : Polynomial ℕ) :
    P.eval b = P.coeff 0 + b * P.divX.eval b := by
  have h := congrArg (Polynomial.eval b) P.X_mul_divX_add
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    add_comm] using h.symm

private theorem div_pow_mod_eval_eq_coeff (b : ℕ) (hb : b > 0) (P : Polynomial ℕ)
    (n : ℕ) (hP : ∀ i ≤ n, P.coeff i < b) :
    P.eval b / b^n % b = P.coeff n := by
  induction n generalizing P with
  | zero =>
    rw [pow_zero, Nat.div_one, eval_eq_coeff_zero_add_mul_divX, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hP 0 (Nat.zero_le _))]
  | succ n ih =>
    have hd : ∀ i ≤ n, P.divX.coeff i < b := fun i hi ↦ by
      simpa only [coeff_divX] using hP (i+1) (Nat.succ_le_succ hi)
    rw [pow_succ', ← Nat.div_div_eq_div_mul, eval_eq_coeff_zero_add_mul_divX,
      Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (hP 0 (Nat.zero_le _)), zero_add, ih P.divX hd, coeff_divX]

/-- The first `n` coefficients of the product of nonnegative polynomials,
computed by one packed multiplication. -/
def multiplyPackedNaturalPolynomial (n : ℕ) (l r : List ℕ) : List ℕ :=
  let w := (l.sum * r.sum).log2 + 1
  let z := packPolynomialDigits w l * packPolynomialDigits w r
  List.ofFn fun i : Fin n ↦ (z >>> (w * (i : ℕ))) % (1 <<< w)

theorem getD_multiplyPackedNaturalPolynomial (n : ℕ) (l r : List ℕ) (i : Fin n) :
    (multiplyPackedNaturalPolynomial n l r).getD i 0 =
      (coefficientListPolynomial l * coefficientListPolynomial r).coeff i := by
  let w := (l.sum * r.sum).log2 + 1
  have hwidth (k : ℕ) :
      (coefficientListPolynomial l * coefficientListPolynomial r).coeff k < 2^w := by
    apply (coeff_le_eval_one _ k).trans_lt
    rw [Polynomial.eval_mul, eval_one_coefficientListPolynomial, eval_one_coefficientListPolynomial]
    exact Nat.lt_log2_self
  simp only [multiplyPackedNaturalPolynomial, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dif_pos, Option.getD_some, Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft,
    packPolynomialDigits_eq_eval, ← Polynomial.eval_mul]
  rw [pow_mul]
  exact div_pow_mod_eval_eq_coeff _ (Nat.two_pow_pos _) _ i (fun j _ ↦ hwidth j)

private def positiveDigits (l : List ℤ) : List ℕ := l.map Int.toNat

private def negativeDigits (l : List ℤ) : List ℕ := l.map fun z ↦ (-z).toNat

private theorem coefficientListPolynomial_eq_pos_sub_neg (l : List ℤ) :
    coefficientListPolynomial l =
      (coefficientListPolynomial (positiveDigits l)).map (Nat.castRingHom ℤ) -
        (coefficientListPolynomial (negativeDigits l)).map (Nat.castRingHom ℤ) := by
  ext k
  simp only [coeff_sub, coeff_map, coeff_coefficientListPolynomial, positiveDigits,
    negativeDigits, List.getD_eq_getElem?_getD, List.getElem?_map, Nat.coe_castRingHom]
  by_cases h : k < l.length
  · simp only [List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]
    exact (Int.toNat_sub_toNat_neg _).symm
  · simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt h)]

/-- The first `n` coefficients of the product of integer polynomials.
Each of the four natural products uses exact packed multiplication. -/
def multiplyPackedIntegerPolynomial (n : ℕ) (l r : List ℤ) : List ℤ :=
  let lp := positiveDigits l
  let ln := negativeDigits l
  let rp := positiveDigits r
  let rn := negativeDigits r
  let pp := multiplyPackedNaturalPolynomial n lp rp
  let mm := multiplyPackedNaturalPolynomial n ln rn
  let pm := multiplyPackedNaturalPolynomial n lp rn
  let mp := multiplyPackedNaturalPolynomial n ln rp
  List.ofFn fun i : Fin n ↦ (pp.getD i 0 : ℤ) + (mm.getD i 0 : ℤ) -
    ((pm.getD i 0 : ℤ) + (mp.getD i 0 : ℤ))

theorem getD_multiplyPackedIntegerPolynomial (n : ℕ) (l r : List ℤ) (i : Fin n) :
    (multiplyPackedIntegerPolynomial n l r).getD i 0 =
      (coefficientListPolynomial l * coefficientListPolynomial r).coeff i := by
  simp only [multiplyPackedIntegerPolynomial, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dif_pos, Option.getD_some]
  change ((multiplyPackedNaturalPolynomial n (positiveDigits l) (positiveDigits r)).getD i 0 : ℤ) +
      ((multiplyPackedNaturalPolynomial n (negativeDigits l) (negativeDigits r)).getD i 0 : ℤ) -
      (((multiplyPackedNaturalPolynomial n (positiveDigits l) (negativeDigits r)).getD i 0 : ℤ) +
       ((multiplyPackedNaturalPolynomial n (negativeDigits l) (positiveDigits r)).getD i 0 : ℤ)) = _
  simp only [getD_multiplyPackedNaturalPolynomial]
  have hmap (a b : List ℕ) :
      ((coefficientListPolynomial a * coefficientListPolynomial b).coeff (i : ℕ) : ℤ) =
        ((coefficientListPolynomial a).map (Nat.castRingHom ℤ) *
          (coefficientListPolynomial b).map (Nat.castRingHom ℤ)).coeff (i : ℕ) := by
    rw [← Polynomial.map_mul, coeff_map]
    rfl
  simp only [hmap, ← coeff_add, ← coeff_sub]
  rw [coefficientListPolynomial_eq_pos_sub_neg l, coefficientListPolynomial_eq_pos_sub_neg r]
  congr 1
  ring

@[simp]
theorem length_multiplyPackedIntegerPolynomial (n : ℕ) (l r : List ℤ) :
    (multiplyPackedIntegerPolynomial n l r).length = n := by
  simp [multiplyPackedIntegerPolynomial]

/-- Power modulo a fixed modulus, reducing after each multiplication. -/
def packedPowMod (a m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | k + 1 => (a * packedPowMod a m k) % m

private theorem packedPowMod_eq (a m k : ℕ) : packedPowMod a m k = a^k % m := by
  induction k with
  | zero => simp [packedPowMod]
  | succ k ih => rw [packedPowMod, ih, Nat.mul_mod_mod, pow_succ']

/-- Store the first `N` packed digits of a power at a specified digit width. -/
def packedNaturalPolynomialPowerAtWidth (N : ℕ) (l : List ℕ) (k w : ℕ) : ℕ × ℕ :=
  (w, packedPowMod (packPolynomialDigits w l) (1 <<< (w*N)) k)

/-- Store the truncated packed power and its uniform digit width. -/
def packedNaturalPolynomialPower (N : ℕ) (l : List ℕ) (k : ℕ) : ℕ × ℕ :=
  packedNaturalPolynomialPowerAtWidth N l k ((l.sum ^ k).log2 + 1)

/-- Extract one coefficient from a packed power. -/
def packedNaturalPolynomialPowerCoeff (a : ℕ × ℕ) (i : ℕ) : ℕ :=
  (a.2 >>> (a.1*i)) % (1 <<< a.1)

private theorem div_pow_mod_truncated {b n i : ℕ} (z : ℕ) (hi : i < n) :
    (z % b^n) / b^i % b = z / b^i % b := by
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, Nat.mod_mod_of_dvd _ (pow_dvd_pow b (Nat.succ_le_of_lt hi)),
    pow_succ, Nat.mod_mul_right_div_self]

/-- Only the low coefficients need to fit the chosen width. -/
theorem packedNaturalPolynomialPowerCoeff_eq_of_prefixBound (N : ℕ) (l : List ℕ)
    (k w i : ℕ) (hi : i < N) (hwidth : ∀ j < N, (coefficientListPolynomial l ^ k).coeff j < 2^w) :
    packedNaturalPolynomialPowerCoeff (packedNaturalPolynomialPowerAtWidth N l k w) i =
      (coefficientListPolynomial l ^ k).coeff i := by
  simp only [packedNaturalPolynomialPowerCoeff, packedNaturalPolynomialPowerAtWidth, packedPowMod_eq,
    Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, packPolynomialDigits_eq_eval, ← Polynomial.eval_pow]
  rw [pow_mul, pow_mul, div_pow_mod_truncated _ hi]
  exact div_pow_mod_eval_eq_coeff _ (Nat.two_pow_pos _) _ i (fun j hj ↦ hwidth j (hj.trans_lt hi))

theorem packedNaturalPolynomialPowerCoeff_eq (N : ℕ) (l : List ℕ) (k i : ℕ) (hi : i < N) :
    packedNaturalPolynomialPowerCoeff (packedNaturalPolynomialPower N l k) i =
      (coefficientListPolynomial l ^ k).coeff i := by
  apply packedNaturalPolynomialPowerCoeff_eq_of_prefixBound N l k _ i hi
  intro j _
  apply (coeff_le_eval_one _ j).trans_lt
  rw [Polynomial.eval_pow, eval_one_coefficientListPolynomial]
  exact Nat.lt_log2_self

private theorem packPolynomialDigits_append (w : ℕ) (l r : List ℕ) :
    packPolynomialDigits w (l ++ r) = packPolynomialDigits w l +
      (packPolynomialDigits w r <<< (w*l.length)) := by
  induction l with
  | nil => simp [packPolynomialDigits]
  | cons c l ih =>
    rw [List.cons_append, packPolynomialDigits, ih, packPolynomialDigits, List.length_cons]
    simp only [Nat.shiftLeft_eq, Nat.mul_succ, pow_add]
    ring

/-- Pack consecutive blocks separately to bound the sizes of intermediate integers. -/
def packPolynomialDigitChunks (w : ℕ) : List (List ℕ) → ℕ
  | [] => 0
  | l :: ls => packPolynomialDigits w l + (packPolynomialDigitChunks w ls <<< (w*l.length))

theorem packPolynomialDigitChunks_eq (w : ℕ) (ls : List (List ℕ)) :
    packPolynomialDigitChunks w ls = packPolynomialDigits w ls.flatten := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [packPolynomialDigitChunks, List.flatten_cons, packPolynomialDigits_append, ih]

/-- Store a truncated power using consecutive input blocks and an explicit width. -/
def packedNaturalPolynomialPowerAtChunkWidth (N : ℕ) (ls : List (List ℕ)) (k w : ℕ) :
    ℕ × ℕ :=
  (w, packedPowMod (packPolynomialDigitChunks w ls) (1 <<< (w*N)) k)

theorem packedNaturalPolynomialPowerAtChunkWidth_eq (N : ℕ) (ls : List (List ℕ))
    (k w : ℕ) :
    packedNaturalPolynomialPowerAtChunkWidth N ls k w =
      packedNaturalPolynomialPowerAtWidth N ls.flatten k w := by
  rw [packedNaturalPolynomialPowerAtChunkWidth, packPolynomialDigitChunks_eq,
    packedNaturalPolynomialPowerAtWidth]

end GRHArticle.SingularModuli
