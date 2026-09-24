import Diophantine.Paper1976.Theorem212

/-!
# JSWW 1976, Theorem 1: the prime-representing polynomial

> **Theorem 1.** The set of prime numbers is identical with the set of positive values
> taken on by the polynomial (1), of degree 25 in the 26 variables `a, b, …, z`, as the
> variables range over the nonnegative integers.

The polynomial is `(k+2){1 - Σ (bracket)²}` where the fourteen brackets are the
equations of Theorem 2.12 with `k` replaced by `k+1`.  We define it as an
integer-valued function of 26 natural numbers and prove the two halves of
Theorem 1: every positive value is prime, and every prime is a value.
-/

namespace JSWW1976

/-- The fourteen bracket expressions of polynomial (1), as integers. -/
def bracket (a b c d e f g h i j k l m n o p q r s t u v w x y z : ℕ) : Fin 14 → ℤ :=
  ![ w * z + h + j - q,
     (g * k + 2 * g + k + 1) * (h + j) + h - z,
     2 * n + p + q + z - e,
     16 * ((k : ℤ) + 1) ^ 3 * (k + 2) * (n + 1) ^ 2 + 1 - f ^ 2,
     (e : ℤ) ^ 3 * (e + 2) * (a + 1) ^ 2 + 1 - o ^ 2,
     ((a : ℤ) ^ 2 - 1) * y ^ 2 + 1 - x ^ 2,
     16 * (r : ℤ) ^ 2 * y ^ 4 * (a ^ 2 - 1) + 1 - u ^ 2,
     (((a : ℤ) + u ^ 2 * (u ^ 2 - a)) ^ 2 - 1) * (n + 4 * d * y) ^ 2 + 1 - (x + c * u) ^ 2,
     n + l + v - y,
     ((a : ℤ) ^ 2 - 1) * l ^ 2 + 1 - m ^ 2,
     a * i + k + 1 - l - i,
     p + l * ((a : ℤ) - n - 1) + b * (2 * a * n + 2 * a - n ^ 2 - 2 * n - 2) - m,
     q + y * ((a : ℤ) - p - 1) + s * (2 * a * p + 2 * a - p ^ 2 - 2 * p - 2) - x,
     z + p * l * ((a : ℤ) - p) + t * (2 * a * p - p ^ 2 - 1) - p * m ]

/-- Polynomial (1) of the article: `(k+2){1 - Σ bracket²}`. -/
def primePoly (a b c d e f g h i j k l m n o p q r s t u v w x y z : ℕ) : ℤ :=
  ((k : ℤ) + 2) * (1 - ∑ ι : Fin 14, (bracket a b c d e f g h i j k l m n o p q r s t u v w x y z ι) ^ 2)

/-- The brackets vanish exactly when the system of Theorem 2.12 holds for `k+1`. -/
theorem brackets_zero_iff (a b c d e f g h i j k l m n o p q r s t u v w x y z : ℕ) :
    (∀ ι, bracket a b c d e f g h i j k l m n o p q r s t u v w x y z ι = 0) ↔
      Thm212System (k + 1) a b c d e f g h i j l m n o p q r s t u v w x y z := by
  simp only [bracket, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Thm212System]
  push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, by linear_combination -h6, by linear_combination -h7,
      by linear_combination -h8, by linear_combination -h10, by linear_combination -h11,
      ?_, by linear_combination -h12, by linear_combination -h13, by linear_combination -h14⟩
    · exact_mod_cast (show (q : ℤ) = w * z + h + j by linear_combination -h1)
    · exact_mod_cast (show (z : ℤ) = (g * (k + 1) + g + (k + 1)) * (h + j) + h by linear_combination -h2)
    · exact_mod_cast (show ((2 * (k + 1)) ^ 3 * (2 * (k + 1) + 2) * (n + 1) ^ 2 + 1 : ℤ) = f * f by
        linear_combination h4)
    · exact_mod_cast (show (e : ℤ) = p + q + z + 2 * n by linear_combination -h3)
    · exact_mod_cast (show ((e : ℤ) ^ 3 * (e + 2) * (a + 1) ^ 2 + 1) = o * o by linear_combination h5)
    · exact_mod_cast (show ((n : ℤ) + l + v) = y by linear_combination h9)
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have h1' : (q : ℤ) = w * z + h + j := by exact_mod_cast h1
    have h2' : (z : ℤ) = (g * (k + 1) + g + (k + 1)) * (h + j) + h := by exact_mod_cast h2
    have h3' : ((2 * (k + 1)) ^ 3 * (2 * (k + 1) + 2) * (n + 1) ^ 2 + 1 : ℤ) = f * f := by
      exact_mod_cast h3
    have h4' : (e : ℤ) = p + q + z + 2 * n := by exact_mod_cast h4
    have h5' : ((e : ℤ) ^ 3 * (e + 2) * (a + 1) ^ 2 + 1) = o * o := by exact_mod_cast h5
    have h11' : ((n : ℤ) + l + v) = y := by exact_mod_cast h11
    refine ⟨by linear_combination -h1', by linear_combination -h2', by linear_combination -h4',
      by linear_combination h3', by linear_combination h5', by linear_combination -h6,
      by linear_combination -h7, by linear_combination -h8, by linear_combination h11',
      by linear_combination -h9, by linear_combination -h10, by linear_combination -h12,
      by linear_combination -h13, ⟨by linear_combination -h14, fun i => i.elim0⟩⟩

/-- A sum of squares of integers is zero only if every term is zero. -/
theorem sum_sq_eq_zero {ι : Type*} [Fintype ι] {f : ι → ℤ} (h : ∑ i, f i ^ 2 = 0) : ∀ i, f i = 0 := by
  intro i
  have hnn : ∀ j, 0 ≤ f j ^ 2 := fun j => sq_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- Theorem 1, first half: every positive value of the polynomial is prime, and equals `k+2`. -/
theorem theorem_1_prime (a b c d e f g h i j k l m n o p q r s t u v w x y z : ℕ)
    (hpos : 0 < primePoly a b c d e f g h i j k l m n o p q r s t u v w x y z) :
    primePoly a b c d e f g h i j k l m n o p q r s t u v w x y z = k + 2 ∧ Nat.Prime (k + 2) := by
  unfold primePoly at hpos ⊢
  set S := ∑ ι : Fin 14, (bracket a b c d e f g h i j k l m n o p q r s t u v w x y z ι) ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun ι _ => sq_nonneg _)
  have hk2 : (0 : ℤ) < (k : ℤ) + 2 := by positivity
  have hS0 : S = 0 := by
    have : 0 < 1 - S := pos_of_mul_pos_right hpos hk2.le
    omega
  have hbr : ∀ ι, bracket a b c d e f g h i j k l m n o p q r s t u v w x y z ι = 0 :=
    sum_sq_eq_zero (f := fun ι => bracket a b c d e f g h i j k l m n o p q r s t u v w x y z ι) hS0
  have hsys := (brackets_zero_iff a b c d e f g h i j k l m n o p q r s t u v w x y z).1 hbr
  refine ⟨by rw [hS0]; ring, ?_⟩
  have := theorem_2_12_of (k := k + 1) (by omega) hsys
  simpa using this

/-- Theorem 1, second half: every prime is a value of the polynomial. -/
theorem theorem_1_exists {P : ℕ} (hP : Nat.Prime P) :
    ∃ a b c d e f g h i j k l m n o p q r s t u v w x y z,
      primePoly a b c d e f g h i j k l m n o p q r s t u v w x y z = P := by
  have h2 : 2 ≤ P := hP.two_le
  obtain ⟨k, rfl⟩ : ∃ k, P = k + 2 := ⟨P - 2, by omega⟩
  obtain ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, hsys⟩ :=
    theorem_2_12_exists (k := k + 1) (by omega) (by simpa using hP)
  refine ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, ?_⟩
  have hbr := (brackets_zero_iff a b c d e f g h i j k l m n o p q r s t u v w x y z).2 hsys
  unfold primePoly
  have : ∑ ι : Fin 14, (bracket a b c d e f g h i j k l m n o p q r s t u v w x y z ι) ^ 2 = 0 :=
    Finset.sum_eq_zero (fun ι _ => by rw [hbr ι]; ring)
  rw [this]; push_cast; ring

/-- Theorem 1: the set of primes is exactly the set of positive values of polynomial (1). -/
theorem theorem_1 (P : ℕ) :
    Nat.Prime P ↔ ∃ a b c d e f g h i j k l m n o p q r s t u v w x y z,
      0 < primePoly a b c d e f g h i j k l m n o p q r s t u v w x y z ∧
      primePoly a b c d e f g h i j k l m n o p q r s t u v w x y z = P := by
  constructor
  · intro hP
    obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, hv⟩ :=
      theorem_1_exists hP
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z,
      by rw [hv]; exact_mod_cast hP.pos, hv⟩
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, hpos, hv⟩
    obtain ⟨hval, hprime⟩ := theorem_1_prime a b c d e f g h i j k l m n o p q r s t u v w x y z hpos
    have : P = k + 2 := by exact_mod_cast hv.symm.trans hval
    rw [this]; exact hprime

end JSWW1976
