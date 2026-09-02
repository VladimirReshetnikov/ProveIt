import FabiusFunction.BellComposition
import FabiusFunction.BernoulliStirling

/-!
# Summation identities for the Stirling triangles

Four families of finite sums for the unsigned Stirling numbers of the first
kind `c(n,k)` and of the second kind `S(n,k)`:

* the two-sum identities `c(n+1,k+1) = ∑_j c(n,j) C(j,k) = ∑_j n^{\underline{n-j}} c(j,k)`
  and `S(n+1,k+1) = ∑_j C(n,j) S(j,k) = ∑_j (k+1)^{n-j} S(j,k)`;
* the hockey-stick identities `c(n+k+1,k) = ∑_{j ≤ k} (n+j) c(n+j,j)` and
  `S(n+k+1,k) = ∑_{j ≤ k} j S(n+j,j)`, telescoping the recurrences;
* the convolutions `C(ℓ+m,ℓ) c(n,ℓ+m) = ∑_j C(n,j) c(j,ℓ) c(n-j,m)` and the
  same for `S`, from the block-colour convolution of partial Bell polynomials.

## Main results

* `stirlingFirst_succ_succ_eq_sum_descFactorial`,
  `stirlingSecond_succ_succ_eq_sum_pow`.
* `stirlingFirst_add_succ_eq_sum`, `stirlingSecond_add_succ_eq_sum`.
* `choose_mul_stirlingFirst_add`, `choose_mul_stirlingSecond_add`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### Two-sum identities -/

/-- `c(n+1,k+1) = ∑_{j ≤ n} n^{\underline{n-j}} c(j,k)`, i.e. `∑_j (n!/j!) c(j,k)`:
the recurrence `c(n+1,k+1) = n c(n,k+1) + c(n,k)` iterated in `n`. -/
theorem stirlingFirst_succ_succ_eq_sum_descFactorial (n k : ℕ) :
    Nat.stirlingFirst (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), n.descFactorial (n - j) * Nat.stirlingFirst j k := by
  induction n with
  | zero => simp [Nat.stirlingFirst_succ_succ]
  | succ n ih =>
    rw [Nat.stirlingFirst_succ_succ, ih,
      Finset.sum_range_succ
        (fun j => (n + 1).descFactorial (n + 1 - j) * Nat.stirlingFirst j k) (n + 1),
      Nat.sub_self, Nat.descFactorial_zero, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show n + 1 - j = (n - j) + 1 by omega, Nat.succ_descFactorial_succ]
    ring

/-- `S(n+1,k+1) = ∑_{j ≤ n} (k+1)^{n-j} S(j,k)`: the recurrence
`S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)` iterated in `n`. -/
theorem stirlingSecond_succ_succ_eq_sum_pow (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), (k + 1) ^ (n - j) * Nat.stirlingSecond j k := by
  induction n with
  | zero => simp [Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    rw [Nat.stirlingSecond_succ_succ, ih,
      Finset.sum_range_succ (fun j => (k + 1) ^ (n + 1 - j) * Nat.stirlingSecond j k) (n + 1),
      Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
    ring

/-! ### Hockey-stick identities -/

/-- `S(n+k+1, k) = ∑_{j ≤ k} j S(n+j, j)`. -/
theorem stirlingSecond_add_succ_eq_sum (n k : ℕ) :
    Nat.stirlingSecond (n + k + 1) k =
      ∑ j ∈ Finset.range (k + 1), j * Nat.stirlingSecond (n + j) j := by
  induction k with
  | zero => simp [Nat.stirlingSecond_succ_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, show n + (k + 1) + 1 = n + k + 1 + 1 by omega,
      Nat.stirlingSecond_succ_succ, show n + (k + 1) = n + k + 1 by omega]
    ring

/-- `c(n+k+1, k) = ∑_{j ≤ k} (n+j) c(n+j, j)`. -/
theorem stirlingFirst_add_succ_eq_sum (n k : ℕ) :
    Nat.stirlingFirst (n + k + 1) k =
      ∑ j ∈ Finset.range (k + 1), (n + j) * Nat.stirlingFirst (n + j) j := by
  induction k with
  | zero =>
    cases n with
    | zero => simp
    | succ n => simp [Nat.stirlingFirst_succ_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, show n + (k + 1) + 1 = n + k + 1 + 1 by omega,
      Nat.stirlingFirst_succ_succ, show n + (k + 1) = n + k + 1 by omega]
    ring

/-! ### Convolutions -/

/-- `B_{n,k}(0!, 1!, 2!, …) = c(n,k)` in `ℚ`. -/
theorem partialBell_factorial_pred_cast (n k : ℕ) :
    partialBell (fun j => ((j - 1).factorial : ℚ)) n k = Nat.stirlingFirst n k := by
  have h := map_partialBell (Nat.castRingHom ℚ) (fun j => (j - 1).factorial) n k
  simp only [Nat.coe_castRingHom] at h
  rw [← h, partialBell_factorial_pred]

/-- **Second-kind convolution:**
`C(ℓ+m,ℓ) S(n,ℓ+m) = ∑_{j ≤ n} C(n,j) S(j,ℓ) S(n-j,m)`. -/
theorem choose_mul_stirlingSecond_add (n l m : ℕ) :
    (l + m).choose l * Nat.stirlingSecond n (l + m) =
      ∑ j ∈ Finset.range (n + 1),
        n.choose j * (Nat.stirlingSecond j l * Nat.stirlingSecond (n - j) m) := by
  have h := factorial_mul_partialBell_add (A := ℚ) (fun _ => (1 : ℚ)) l m n
  simp only [partialBell_one_cast] at h
  have hfac : ((l + m).choose l : ℚ) * l.factorial * m.factorial = (l + m).factorial := by
    rw [Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial l m
  have hlm : (l.factorial : ℚ) * m.factorial ≠ 0 := by positivity
  have hQ : ((l + m).choose l : ℚ) * Nat.stirlingSecond n (l + m) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℚ) * (Nat.stirlingSecond j l * Nat.stirlingSecond (n - j) m) := by
    apply mul_right_cancel₀ hlm
    calc ((l + m).choose l : ℚ) * Nat.stirlingSecond n (l + m) * (l.factorial * m.factorial)
        = ((l + m).choose l : ℚ) * l.factorial * m.factorial * Nat.stirlingSecond n (l + m) := by
          ring
      _ = ((l + m).factorial : ℚ) * Nat.stirlingSecond n (l + m) := by rw [hfac]
      _ = (l.factorial : ℚ) * m.factorial * ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℚ) * (Nat.stirlingSecond j l * Nat.stirlingSecond (n - j) m) := h
      _ = _ := by ring
  exact_mod_cast hQ

/-- **First-kind convolution:**
`C(ℓ+m,ℓ) c(n,ℓ+m) = ∑_{j ≤ n} C(n,j) c(j,ℓ) c(n-j,m)`. -/
theorem choose_mul_stirlingFirst_add (n l m : ℕ) :
    (l + m).choose l * Nat.stirlingFirst n (l + m) =
      ∑ j ∈ Finset.range (n + 1),
        n.choose j * (Nat.stirlingFirst j l * Nat.stirlingFirst (n - j) m) := by
  have h := factorial_mul_partialBell_add (A := ℚ) (fun j => ((j - 1).factorial : ℚ)) l m n
  simp only [partialBell_factorial_pred_cast] at h
  have hfac : ((l + m).choose l : ℚ) * l.factorial * m.factorial = (l + m).factorial := by
    rw [Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial l m
  have hlm : (l.factorial : ℚ) * m.factorial ≠ 0 := by positivity
  have hQ : ((l + m).choose l : ℚ) * Nat.stirlingFirst n (l + m) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℚ) * (Nat.stirlingFirst j l * Nat.stirlingFirst (n - j) m) := by
    apply mul_right_cancel₀ hlm
    calc ((l + m).choose l : ℚ) * Nat.stirlingFirst n (l + m) * (l.factorial * m.factorial)
        = ((l + m).choose l : ℚ) * l.factorial * m.factorial * Nat.stirlingFirst n (l + m) := by
          ring
      _ = ((l + m).factorial : ℚ) * Nat.stirlingFirst n (l + m) := by rw [hfac]
      _ = (l.factorial : ℚ) * m.factorial * ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℚ) * (Nat.stirlingFirst j l * Nat.stirlingFirst (n - j) m) := h
      _ = _ := by ring
  exact_mod_cast hQ

end Fabius
