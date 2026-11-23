import FiniteInversion

/-!
# Formal Möbius series through each finite degree

All arithmetic is integral. The scaled coefficients of L are n [X^n] L,
and the scaled coefficients of exp L are n! [X^n] exp L. Thus no rational
or power-series library is needed. Rows of FiniteInversion use index n-1
for a positive degree n.
-/
namespace MobiusSeries
open FiniteInversion

/-- Coefficients of the positive multiples of d. -/
def ray (d n : Nat) : Int :=
  if n = 0 then 0 else if n % d = 0 then 1 else 0

def shift (d : Nat) (f : Nat → Int) (n : Nat) : Int :=
  if d ≤ n then f (n-d) else 0

/-- (1-X^d)G_d = X^d uniquely characterizes the geometric series G_d. -/
theorem ray_equation (d n : Nat) (hd : 0 < d) :
    ray d n - shift d (ray d) n = (if n = d then 1 else 0) := by
  by_cases hlt : n < d
  · have hn : n ≠ d := by omega
    simp [ray, shift, Nat.mod_eq_of_lt hlt, Nat.not_le_of_lt hlt, hn]
  · by_cases heq : n = d
    · subst n
      simp [ray, shift, Nat.ne_of_gt hd]
    · have hsub : n-d ≠ 0 := by omega
      have hn : n ≠ 0 := by omega
      have hmod : n % d = (n-d) % d := by
        conv => lhs; rw [show n = (n-d)+d by omega]
        exact Nat.add_mod_right _ _
      simp [ray, shift, Nat.le_of_not_gt hlt, hn, heq, hsub, hmod]

/-- Coefficient of X^n in the sum of a(d) X^d/(1-X^d), d ≥ 1. -/
def lambert (a : Nat → Int) (n : Nat) : Int :=
  total (fun j => ray (j+1) n * a (j+1)) n

theorem lambert_is_divisor_sum (a : Nat → Int) (i : Nat) :
    lambert a (i+1) = divisorSum a i := by
  unfold lambert divisorSum integrate lower
  rw [total]
  have h : total (fun j => ray (j+1) (i+1) * a (j+1)) i =
      total (fun j => dividesWeight i j * a (j+1)) i := by
    apply total_congr
    intro j _
    simp [ray, dividesWeight]
  rw [h]
  simp [ray, Int.add_comm]

theorem mobius_lambert (n : Nat) :
    lambert mu n = (if n = 1 then 1 else 0) := by
  cases n with
  | zero => rfl
  | succ i =>
    rw [lambert_is_divisor_sum, divisor_cancellation]
    cases i <;> rfl

/-- Raw numerator and denominator in the term -(a(d)/d)X^(dj)/j. -/
structure Fraction where
  num : Int
  den : Nat

def factorLogCoeff (a : Nat → Int) (d n : Nat) : Fraction :=
  if n ≠ 0 ∧ n % d = 0 then ⟨-a d, d*(n/d)⟩ else ⟨0,1⟩

theorem factorLogCoeff_scaled (a : Nat → Int) (d n : Nat) :
    (n : Int) * (factorLogCoeff a d n).num =
      -(ray d n * a d) * ((factorLogCoeff a d n).den : Int) := by
  by_cases h : n ≠ 0 ∧ n % d = 0
  · have hd := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.2)
    simp [factorLogCoeff, h, ray, hd, Int.mul_comm]
  · by_cases hn : n = 0
    · simp [factorLogCoeff, ray, hn]
    · have hr : n % d ≠ 0 := by intro hz; exact h ⟨hn,hz⟩
      simp [factorLogCoeff, ray, hn, hr]

/-- Sum of the scaled logarithmic coefficients in degree n. -/
def logNumerator (a : Nat → Int) (n : Nat) : Int :=
  total (fun j => -(ray (j+1) n * a (j+1))) n

theorem logNumerator_eq (a : Nat → Int) (n : Nat) :
    logNumerator a n = -lambert a n := by
  have neg_total (f : Nat → Int) (k : Nat) :
      total (fun j => -f j) k = -total f k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [total, ih]; omega
  exact neg_total (fun j => ray (j+1) n * a (j+1)) n

theorem mobius_logarithm (n : Nat) :
    logNumerator mu n = (if n = 1 then -1 else 0) := by
  rw [logNumerator_eq, mobius_lambert]
  split <;> decide

/-- n!/(n-k)! for k ≤ n. -/
def falling (n : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => falling n k * (n-k)

/-- The coefficient rule for E' = L'E, in factorial-scaled coordinates.
The k=0 term is separated to leave a sum over k=1,...,n. -/
def expStep (l e : Nat → Int) (n : Nat) : Int :=
  l 1 * e n + total (fun j => (falling n (j+1) : Int) * l (j+2) * e (n-(j+1))) n

theorem mobius_exp_step (e : Nat → Int) (n : Nat) :
    expStep (logNumerator mu) e n = -e n := by
  have hzero (k : Nat) : total (fun _ => (0:Int)) k = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [total, ih]
  unfold expStep
  rw [mobius_logarithm]
  simp only [↓reduceIte, Int.neg_one_mul]
  have hz : total (fun j => (falling n (j+1) : Int) * logNumerator mu (j+2) *
      e (n-(j+1))) n = total (fun _ => 0) n := by
    apply total_congr
    intro j _
    rw [mobius_logarithm, if_neg (by omega)]
    simp
  rw [hz, hzero, Int.add_zero]

theorem mobius_exponential (e : Nat → Int) :
    (e 0 = 1 ∧ ∀ n, e (n+1) = expStep (logNumerator mu) e n) ↔
    (∀ n, e n = (-1 : Int)^n) := by
  constructor
  · rintro ⟨h0, hs⟩ n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      rw [hs, mobius_exp_step, ih, Int.pow_succ, Int.mul_neg_one]
  · intro h
    constructor
    · simpa using h 0
    · intro n
      rw [mobius_exp_step, h (n+1), h n, Int.pow_succ, Int.mul_neg_one]

end MobiusSeries
