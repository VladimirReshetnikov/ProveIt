import FabiusFunction.BellShiftEGF
import FabiusFunction.StirlingBasisChange

/-!
# The Bell umbra and the weighted Bell shift

The Bell umbra is the linear functional `L : R[x] → R` with `L(x^n) = B_n` (Bell numbers).
Touchard's recurrence `B_{n+1} = ∑_j C(n,j) B_j` says exactly that `L(x f(x)) = L(f(x+1))`
(`bellUmbra_X_mul`), and iterating it gives the umbral shift
`L((x)_k f(x)) = L(f(x+k))` for the falling factorial `(x)_k` (`bellUmbra_descPochhammer_mul`).
Since `(x)_k = ∑_i s(k,i) x^i` with the signed Stirling numbers of the first kind, this is the
weighted Bell shift

`∑_j C(n,j) a^j b^{n-j} B_j = ∑_i s(k,i) ∑_j C(n,j) a^j (b - ak)^{n-j} B_{j+i}`

(`weighted_bell_shift`), with the special cases `k = 1` (`weighted_bell_shift_one`) and
`a = 1, b = k` (`sum_signedStirlingFirst_mul_bell_eq`), all over an arbitrary commutative ring.

## Main results

* `bellUmbra`, `bellUmbra_monomial`, `bellUmbra_C_mul_X_pow`, `bellUmbra_X_pow`,
  `bellUmbra_C_mul`.
* `bellUmbra_X_mul`, `bellUmbra_descPochhammer_mul`, `bellUmbra_descPochhammer`.
* `sum_signedStirlingFirst_mul_bell_eq`, `weighted_bell_shift`, `weighted_bell_shift_one`.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

variable (R : Type*) [CommRing R]

/-- The Bell umbra: the `R`-linear functional on `R[x]` with `L(x^n) = B_n`. -/
noncomputable def bellUmbra : R[X] →ₗ[R] R where
  toFun f := f.sum fun i a => a * (Nat.bell i : R)
  map_add' f g :=
    Polynomial.sum_add_index f g _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Polynomial.sum_smul_index _ _ _ (fun _ => zero_mul _), Polynomial.sum_def,
      Polynomial.sum_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

/-- `L(a x^n) = a B_n`. -/
theorem bellUmbra_monomial (n : ℕ) (a : R) : bellUmbra R (monomial n a) = a * Nat.bell n := by
  show (monomial n a : R[X]).sum (fun i b => b * (Nat.bell i : R)) = a * Nat.bell n
  exact Polynomial.sum_monomial_index a _ (zero_mul _)

/-- `L(a x^n) = a B_n`. -/
theorem bellUmbra_C_mul_X_pow (a : R) (n : ℕ) : bellUmbra R (C a * X ^ n) = a * Nat.bell n := by
  rw [C_mul_X_pow_eq_monomial, bellUmbra_monomial]

/-- `L(x^n) = B_n`. -/
theorem bellUmbra_X_pow (n : ℕ) : bellUmbra R (X ^ n) = Nat.bell n := by
  rw [← one_mul (X ^ n : R[X]), ← C_1, bellUmbra_C_mul_X_pow, one_mul]

/-- `L(1) = 1`. -/
theorem bellUmbra_one : bellUmbra R 1 = 1 := by
  rw [← pow_zero (X : R[X]), bellUmbra_X_pow, Nat.bell_zero, Nat.cast_one]

/-- `L(a f) = a L(f)`. -/
theorem bellUmbra_C_mul (a : R) (f : R[X]) : bellUmbra R (C a * f) = a * bellUmbra R f := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- **Touchard's recurrence, umbrally:** `L(x f(x)) = L(f(x+1))`. -/
theorem bellUmbra_X_mul (f : R[X]) : bellUmbra R (X * f) = bellUmbra R (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, add_comp, map_add]
  | monomial n a =>
    have hL : (X : R[X]) * monomial n a = C a * X ^ (n + 1) := by
      rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_succ']
    have hR : (monomial n a : R[X]).comp (X + 1) =
        ∑ j ∈ range (n + 1), C (a * (n.choose j : R)) * X ^ j := by
      rw [← C_mul_X_pow_eq_monomial, C_mul_comp, pow_comp, X_comp, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [one_pow, mul_one, C_mul, C_eq_natCast]
      ring
    rw [hL, hR, bellUmbra_C_mul_X_pow, map_sum]
    simp only [bellUmbra_C_mul_X_pow]
    rw [bell_succ_eq_sum_choose, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring

/-- **The umbral shift:** `L((x)_k f(x)) = L(f(x+k))` for the falling factorial `(x)_k`. -/
theorem bellUmbra_descPochhammer_mul (k : ℕ) (f : R[X]) :
    bellUmbra R (descPochhammer R k * f) = bellUmbra R (f.comp (X + (k : R[X]))) := by
  induction k generalizing f with
  | zero => rw [descPochhammer_zero, one_mul, Nat.cast_zero, add_zero, comp_X]
  | succ k ih =>
    rw [descPochhammer_succ_left, mul_assoc, bellUmbra_X_mul, mul_comp, comp_assoc, sub_comp,
      X_comp, one_comp, add_sub_cancel_right, comp_X, ih, comp_assoc, add_comp, X_comp, one_comp,
      Nat.cast_succ, add_assoc]

/-- All factorial moments of the Bell umbra are `1`: `L((x)_k) = 1`. -/
theorem bellUmbra_descPochhammer (k : ℕ) : bellUmbra R (descPochhammer R k) = 1 := by
  rw [← mul_one (descPochhammer R k), bellUmbra_descPochhammer_mul, one_comp, bellUmbra_one]

/-- **The `k`-fold Bell shift:** `∑_i s(k,i) B_{n+i} = ∑_j C(n,j) k^{n-j} B_j`
(the signed first-kind numbers `s(k,i) = (-1)^{k-i} c(k,i)`). -/
theorem sum_signedStirlingFirst_mul_bell_eq (k n : ℕ) :
    ∑ i ∈ range (k + 1), (signedStirlingFirst k i : R) * Nat.bell (n + i)
      = ∑ j ∈ range (n + 1), (n.choose j : R) * (k : R) ^ (n - j) * Nat.bell j := by
  have hL : ∀ i, (monomial i (signedStirlingFirst k i : R) : R[X]) * X ^ n =
      C (signedStirlingFirst k i : R) * X ^ (n + i) := fun i => by
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add, add_comm]
  have hR : ∀ j, (X : R[X]) ^ j * (k : R[X]) ^ (n - j) * (n.choose j : R[X]) =
      C ((n.choose j : R) * (k : R) ^ (n - j)) * X ^ j := fun j => by
    simp only [C_mul, C_pow, C_eq_natCast]
    ring
  have h := bellUmbra_descPochhammer_mul R k (X ^ n)
  rw [descPochhammer_eq_sum_monomial_signedStirlingFirst, Finset.sum_mul, pow_comp, X_comp,
    add_pow] at h
  simp only [hL, hR, map_sum, bellUmbra_C_mul_X_pow] at h
  exact h

/-- **The weighted Bell shift:**
`∑_j C(n,j) a^j b^{n-j} B_j = ∑_i s(k,i) ∑_j C(n,j) a^j (b - ak)^{n-j} B_{j+i}`. -/
theorem weighted_bell_shift (a b : R) (k n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : R) * a ^ j * b ^ (n - j) * Nat.bell j
      = ∑ i ∈ range (k + 1), (signedStirlingFirst k i : R) *
          ∑ j ∈ range (n + 1),
            (n.choose j : R) * a ^ j * (b - a * k) ^ (n - j) * Nat.bell (j + i) := by
  have hexp : ∀ c : R, ((C a * X + C c) ^ n : R[X]) =
      ∑ j ∈ range (n + 1), C ((n.choose j : R) * a ^ j * c ^ (n - j)) * X ^ j := fun c => by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_pow, C_mul, C_pow, C_eq_natCast]
    ring
  have hcomp : ((C a * X + C (b - a * k)) ^ n : R[X]).comp (X + (k : R[X])) =
      (C a * X + C b) ^ n := by
    rw [pow_comp, add_comp, C_mul_comp, X_comp, C_comp]
    congr 1
    rw [map_sub, map_mul, C_eq_natCast]
    ring
  have hprod : descPochhammer R k * (C a * X + C (b - a * k)) ^ n =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (n + 1),
        C ((signedStirlingFirst k i : R) * ((n.choose j : R) * a ^ j * (b - a * k) ^ (n - j))) *
          X ^ (i + j) := by
    rw [descPochhammer_eq_sum_monomial_signedStirlingFirst, hexp, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [← C_mul_X_pow_eq_monomial, C_mul, C_pow]
    ring
  have h := bellUmbra_descPochhammer_mul R k ((C a * X + C (b - a * k)) ^ n)
  rw [hcomp, hprod, hexp b, map_sum, map_sum] at h
  simp only [map_sum, bellUmbra_C_mul_X_pow] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm i j]
  ring

/-- The case `k = 1`: `∑_j C(n,j) a^j b^{n-j} B_j = ∑_j C(n,j) a^j (b - a)^{n-j} B_{j+1}`. -/
theorem weighted_bell_shift_one (a b : R) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : R) * a ^ j * b ^ (n - j) * Nat.bell j
      = ∑ j ∈ range (n + 1), (n.choose j : R) * a ^ j * (b - a) ^ (n - j) * Nat.bell (j + 1) := by
  have h := weighted_bell_shift R a b 1 n
  have h0 : signedStirlingFirst 1 0 = 0 := by decide
  have h1 : signedStirlingFirst 1 1 = 1 := by decide
  rw [Finset.sum_range_succ _ 1, Finset.sum_range_one, h0, h1, Int.cast_zero, zero_mul, zero_add,
    Int.cast_one, one_mul, Nat.cast_one, mul_one] at h
  exact h

end Fabius
