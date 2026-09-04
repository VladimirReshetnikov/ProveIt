import FabiusFunction.ExponentialRiordan

/-!
# Ordinary Bell polynomials and the composition of ordinary generating functions

The ordinary partial Bell polynomial `B̂_{n,k}(x_1, x_2, …)` is the sum of
`x_{i_1} ⋯ x_{i_k}` over all compositions `i_1 + ⋯ + i_k = n` with parts `≥ 1`;
it is defined here by the recurrence `B̂_{n,k+1} = ∑_{i=1}^{n} x_i B̂_{n-i,k}`.
For a power series `f` with zero constant term, `[t^n] f^k = B̂_{n,k}(f_1, f_2, …)`,
and hence the **ordinary composition theorem**

`[t^n] g(f(t)) = ∑_{k ≤ n} g_k B̂_{n,k}(f_1, f_2, …)`.

Applied to `g = 1/(1-u)` and `f = -(A - 1)` this gives the coefficients of the
reciprocal of a series with constant term one.

## Main results

* `ordPartialBell`, `ordPartialBell_mul_left`, `ordPartialBell_congr`.
* `coeff_pow_eq_ordPartialBell`: `[t^n] f^k = B̂_{n,k}(f_1, f_2, …)`.
* `coeff_subst_eq_sum_ordPartialBell`: the ordinary composition theorem.
* `reciprocalSeries`, `mul_reciprocalSeries`, `coeff_reciprocalSeries`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Def

variable {R : Type*} [CommSemiring R]

/-- The ordinary partial Bell polynomials, by the recurrence
`B̂_{n,0} = δ_{n,0}`, `B̂_{n,k+1} = ∑_{i=1}^{n} x_i B̂_{n-i,k}`. -/
def ordPartialBell (x : ℕ → R) : ℕ → ℕ → R
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 => ∑ i ∈ Finset.range n, x (i + 1) * ordPartialBell x (n - (i + 1)) k

/-- With no parts, the ordinary partial Bell polynomial is `1` at `n = 0` and `0` otherwise. -/
@[simp]
theorem ordPartialBell_zero_right (x : ℕ → R) (n : ℕ) :
    ordPartialBell x n 0 = if n = 0 then 1 else 0 := by
  rw [ordPartialBell]

/-- Peeling one part off an ordinary partial Bell polynomial, summing over its size. -/
theorem ordPartialBell_succ_right (x : ℕ → R) (n k : ℕ) :
    ordPartialBell x n (k + 1) =
      ∑ i ∈ Finset.range n, x (i + 1) * ordPartialBell x (n - (i + 1)) k := by
  rw [ordPartialBell]

/-- `B̂_{n,k}` only depends on the weights `x_i` with `i ≥ 1`. -/
theorem ordPartialBell_congr {x y : ℕ → R} (h : ∀ i, 1 ≤ i → x i = y i) (n k : ℕ) :
    ordPartialBell x n k = ordPartialBell y n k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [ordPartialBell_succ_right, ordPartialBell_succ_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h (i + 1) (by omega), ih]

/-- Degree homogeneity: `B̂_{n,k}(c x) = c^k B̂_{n,k}(x)`. -/
theorem ordPartialBell_mul_left (c : R) (x : ℕ → R) (n k : ℕ) :
    ordPartialBell (fun i => c * x i) n k = c ^ k * ordPartialBell x n k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [ordPartialBell_succ_right, ordPartialBell_succ_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih]
    ring

end Def

section PowerCoefficients

variable {R : Type*} [CommSemiring R]

/-- `[t^n] f^k = B̂_{n,k}(f_1, f_2, …)` when `f` has zero constant term. -/
theorem coeff_pow_eq_ordPartialBell {f : R⟦X⟧} (hf : constantCoeff f = 0) (n k : ℕ) :
    coeff n (f ^ k) = ordPartialBell (fun i => coeff i f) n k := by
  induction k generalizing n with
  | zero => rw [pow_zero, PowerSeries.coeff_one, ordPartialBell_zero_right]
  | succ k ih =>
    rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ', ordPartialBell_succ_right]
    simp only [Nat.sub_zero, coeff_zero_eq_constantCoeff_apply, hf, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih]

end PowerCoefficients

section Series

variable {R : Type*} [CommRing R]

/-- **The ordinary composition theorem:**
`[t^n] g(f(t)) = ∑_{k ≤ n} g_k B̂_{n,k}(f_1, f_2, …)` when `f` has zero constant term. -/
theorem coeff_subst_eq_sum_ordPartialBell (g : R⟦X⟧) {f : R⟦X⟧} (hf : constantCoeff f = 0)
    (n : ℕ) :
    coeff n (g.subst f) =
      ∑ k ∈ Finset.range (n + 1), coeff k g * ordPartialBell (fun i => coeff i f) n k := by
  have h := coeff_mul_subst_eq R hf 1 g n
  rw [one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_mul, coeff_pow_eq_ordPartialBell hf]

/-- The series `1/(1-u)` at `u = -(A - 1)`, which is the reciprocal of `A` when `A` has
constant term one. -/
noncomputable def reciprocalSeries (A : R⟦X⟧) : R⟦X⟧ :=
  (PowerSeries.mk 1 : R⟦X⟧).subst (-(A - 1))

/-- `A · reciprocalSeries A = 1` when `A` has constant term one. -/
theorem mul_reciprocalSeries {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    A * reciprocalSeries A = 1 := by
  have hs : HasSubst (-(A - 1)) := by
    apply HasSubst.of_constantCoeff_zero'
    rw [map_neg, map_sub, hA, map_one, sub_self, neg_zero]
  have h := congrArg (substAlgHom hs) (mk_one_mul_one_sub_eq_one R)
  rw [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom,
    show (1 : R⟦X⟧) - -(A - 1) = A by ring] at h
  rw [reciprocalSeries, mul_comm]
  exact h

/-- **Coefficients of the reciprocal:** if `A = 1 + ∑_{n ≥ 1} a_n t^n` then
`[t^n] (1/A) = ∑_{k ≤ n} (-1)^k B̂_{n,k}(a_1, a_2, …)`. -/
theorem coeff_reciprocalSeries {A : R⟦X⟧} (hA : constantCoeff A = 1) (n : ℕ) :
    coeff n (reciprocalSeries A) =
      ∑ k ∈ Finset.range (n + 1), (-1) ^ k * ordPartialBell (fun i => coeff i A) n k := by
  have hs : constantCoeff (-(A - 1)) = 0 := by
    rw [map_neg, map_sub, hA, map_one, sub_self, neg_zero]
  rw [reciprocalSeries, coeff_subst_eq_sum_ordPartialBell _ hs]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_mk, Pi.one_apply, one_mul]
  have hx : (fun i => coeff i (-(A - 1))) = fun i => (-1 : R) * coeff i (A - 1) := by
    funext i
    rw [map_neg]
    ring
  rw [hx, ordPartialBell_mul_left]
  congr 1
  apply ordPartialBell_congr
  intro i hi
  rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero]

end Series

end Fabius
