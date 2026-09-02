import FabiusFunction.PartialBellPolynomials
import FabiusFunction.StirlingGeneratingFunctions

/-!
# Exponential generating functions of Bell polynomials

This module develops the exponential-generating-function calculus behind the
labelled decomposition principle, over any commutative `ℚ`-algebra `A`:

* `egfA a = ∑_n a_n X^n/n!` for an `A`-valued sequence, with
  `egfA a * egfA b = egfA (a ⋆ b)` (binomial convolution) and
  `d/dX (egfA a) = egfA (shift a)`;
* the weight series `X(t) = ∑_{j ≥ 1} x_j t^j/j!` of a block-weight sequence
  and the **partial Bell column theorem** `X(t)^k = k! ∑_n B_{n,k}(x) t^n/n!`,
  proved by induction on `k` through the first-order equation both sides
  satisfy (`Y' = (k+1) X' · X^k/k!`) and the uniqueness of solutions;
* the **complete Bell theorem** `exp(X(t)) = ∑_n B_n(x) t^n/n!`, from the
  linear equation `Y' = X' Y`, `Y(0) = 1`, whose solution is unique;
* consequences: `B_{n,k}(0!,1!,2!,…) = c(n,k)` and `B_{n,k}(1!,2!,3!,…) = L(n,k)`
  by comparing with the column generating functions `(-log(1-t))^k/k!` and
  `(t/(1-t))^k/k!` (the latter proved here), and the Bell-number generating
  function `exp(e^t - 1) = ∑_n B_n t^n/n!`.

## Main results

* `egfA`, `coeff_egfA`, `constantCoeff_egfA`, `egfA_mul`, `derivative_egfA`.
* `eq_zero_of_derivative_eq_mul`: `D' = D·g`, `D(0) = 0` forces `D = 0`.
* `bellWeightSeries`, `bellWeightSeries_pow`, `exp_subst_bellWeightSeries`.
* `X_mul_mkOne_pow`: `(t/(1-t))^k = ∑_n k! L(n,k) t^n/n!`.
* `partialBell_factorial_pred`, `partialBell_factorial`,
  `bell_complete_one`, `exp_subst_exp_sub_one`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section EGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The exponential generating function `∑_n a_n X^n/n!` of an `A`-valued
sequence. -/
noncomputable def egfA (a : ℕ → A) : A⟦X⟧ :=
  PowerSeries.mk fun n => algebraMap ℚ A (1 / n.factorial) * a n

@[simp] theorem coeff_egfA (a : ℕ → A) (n : ℕ) :
    coeff n (egfA A a) = algebraMap ℚ A (1 / n.factorial) * a n :=
  coeff_mk _ _

@[simp] theorem constantCoeff_egfA (a : ℕ → A) : constantCoeff (egfA A a) = a 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_egfA]
  simp

/-- The rational-sequence generating function `egf` is the special case of `egfA`. -/
theorem egfA_algebraMap (a : ℕ → ℚ) :
    egfA A (fun n => algebraMap ℚ A (a n)) = egf A a := by
  ext n
  rw [coeff_egfA, coeff_egf, ← map_mul, one_div_mul_eq_div]

/-- **Products of exponential generating functions are binomial convolutions:**
`egfA a * egfA b = egfA (a ⋆ b)`. -/
theorem egfA_mul (a b : ℕ → A) : egfA A a * egfA A b = egfA A (Bell.binomialConv a b) := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_egfA,
    Bell.binomialConv_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [coeff_egfA]
  have hc : ((n.choose k : ℕ) : A) = algebraMap ℚ A (n.choose k) := by simp
  rw [hc, Nat.cast_choose ℚ hkn]
  have h1 : algebraMap ℚ A (1 / k.factorial) * algebraMap ℚ A (1 / (n - k).factorial)
      = algebraMap ℚ A (1 / n.factorial) *
          algebraMap ℚ A (n.factorial / (k.factorial * (n - k).factorial)) := by
    rw [← map_mul, ← map_mul]
    congr 1
    have hk : (k.factorial : ℚ) ≠ 0 := by positivity
    have hnk : ((n - k).factorial : ℚ) ≠ 0 := by positivity
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  calc algebraMap ℚ A (1 / k.factorial) * a k *
        (algebraMap ℚ A (1 / (n - k).factorial) * b (n - k))
      = (algebraMap ℚ A (1 / k.factorial) * algebraMap ℚ A (1 / (n - k).factorial)) *
          (a k * b (n - k)) := by ring
    _ = _ := by
        rw [h1]
        ring

/-- **Differentiation shifts the coefficient sequence:**
`d/dX (egfA a) = egfA (shift a)`. -/
theorem derivative_egfA (a : ℕ → A) : d⁄dX A (egfA A a) = egfA A (Bell.shift a) := by
  ext n
  rw [coeff_derivative, coeff_egfA, coeff_egfA, Bell.shift_apply]
  have h1 : ((n : A) + 1) = algebraMap ℚ A ((n : ℚ) + 1) := by simp
  rw [h1]
  have h2 : algebraMap ℚ A (1 / (n + 1).factorial) * algebraMap ℚ A ((n : ℚ) + 1)
      = algebraMap ℚ A (1 / n.factorial) := by
    rw [← map_mul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  calc algebraMap ℚ A (1 / (n + 1).factorial) * a (n + 1) * algebraMap ℚ A ((n : ℚ) + 1)
      = (algebraMap ℚ A (1 / (n + 1).factorial) * algebraMap ℚ A ((n : ℚ) + 1)) * a (n + 1) := by
        ring
    _ = _ := by rw [h2]

/-- **Uniqueness for the linear equation `D' = D·g`:** a power series over a
`ℚ`-algebra with `D' = D g` and `D(0) = 0` vanishes. -/
theorem eq_zero_of_derivative_eq_mul {D g : A⟦X⟧} (hD : d⁄dX A D = D * g)
    (h0 : constantCoeff D = 0) : D = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, h0, map_zero]
    | succ n =>
      have h := congrArg (coeff n) hD
      rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_eq_zero] at h
      · rw [map_zero]
        have hcast : ((n : A) + 1) = algebraMap ℚ A ((n : ℚ) + 1) := by simp
        have hinv : algebraMap ℚ A ((n : ℚ) + 1) * algebraMap ℚ A (1 / ((n : ℚ) + 1)) = 1 := by
          rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
        rw [hcast] at h
        calc coeff (n + 1) D
            = coeff (n + 1) D *
                (algebraMap ℚ A ((n : ℚ) + 1) * algebraMap ℚ A (1 / ((n : ℚ) + 1))) := by
              rw [hinv, mul_one]
          _ = 0 := by rw [← mul_assoc, h, zero_mul]
      · intro k hk
        have hkn : k < n + 1 := Finset.mem_range.mp hk
        simp [ih k hkn]

/-! ### The weight series and the partial Bell column theorem -/

/-- The block-weight series `X(t) = ∑_{j ≥ 1} x_j t^j / j!`. -/
noncomputable def bellWeightSeries (x : ℕ → A) : A⟦X⟧ :=
  egfA A fun j => if j = 0 then 0 else x j

@[simp] theorem constantCoeff_bellWeightSeries (x : ℕ → A) :
    constantCoeff (bellWeightSeries A x) = 0 := by
  rw [bellWeightSeries, constantCoeff_egfA, if_pos rfl]

/-- `d/dt X(t) = ∑_j x_{j+1} t^j/j!`. -/
theorem derivative_bellWeightSeries (x : ℕ → A) :
    d⁄dX A (bellWeightSeries A x) = egfA A (Bell.shift x) := by
  have hs : Bell.shift (fun j => if j = 0 then (0 : A) else x j) = Bell.shift x := by
    funext j
    simp [Bell.shift_apply]
  rw [bellWeightSeries, derivative_egfA, hs]

/-- **The partial Bell column theorem:** `X(t)^k = k! · ∑_n B_{n,k}(x) t^n/n!`. -/
theorem bellWeightSeries_pow (x : ℕ → A) (k : ℕ) :
    bellWeightSeries A x ^ k = (k.factorial : A) • egfA A fun n => partialBell x n k := by
  induction k with
  | zero =>
    ext n
    rw [pow_zero, coeff_one, coeff_smul, coeff_egfA]
    cases n with
    | zero => simp
    | succ n => simp
  | succ k ih =>
    haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
    have hshift : Bell.shift (fun n => partialBell x n (k + 1))
        = Bell.binomialConv (Bell.shift x) (fun j => partialBell x j k) := by
      funext n
      rw [Bell.shift_apply, partialBell_succ_succ_eq_binomialConv]
    apply derivative.ext
    · rw [derivative_pow, Nat.add_sub_cancel, ih, derivative_bellWeightSeries,
        (d⁄dX A).map_smul, derivative_egfA, hshift, ← egfA_mul]
      simp only [smul_eq_C_mul, map_natCast, Nat.factorial_succ]
      push_cast
      ring
    · rw [map_pow, constantCoeff_bellWeightSeries, zero_pow (Nat.succ_ne_zero k), smul_eq_C_mul,
        map_mul, constantCoeff_C, constantCoeff_egfA, partialBell_zero_succ, mul_zero]

omit [Algebra ℚ A] in
/-- Substituting a series without constant term preserves the constant term. -/
theorem constantCoeff_subst_of_constantCoeff_eq_zero {a f : A⟦X⟧}
    (ha : constantCoeff a = 0) : constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]

/-- **The complete Bell theorem:** `exp(X(t)) = ∑_n B_n(x) t^n/n!`, with
`B_n = Bell.complete x n` the complete Bell polynomials. -/
theorem exp_subst_bellWeightSeries (x : ℕ → A) :
    (exp A).subst (bellWeightSeries A x) = egfA A (Bell.complete x) := by
  have hW : HasSubst (bellWeightSeries A x) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_bellWeightSeries A x)
  have hL : d⁄dX A ((exp A).subst (bellWeightSeries A x))
      = (exp A).subst (bellWeightSeries A x) * egfA A (Bell.shift x) := by
    rw [derivative_subst A hW, derivative_exp, derivative_bellWeightSeries]
  have hR : d⁄dX A (egfA A (Bell.complete x)) = egfA A (Bell.complete x) * egfA A (Bell.shift x) := by
    rw [derivative_egfA, Bell.shift_complete, egfA_mul]
  have hzero := eq_zero_of_derivative_eq_mul A
    (D := (exp A).subst (bellWeightSeries A x) - egfA A (Bell.complete x))
    (g := egfA A (Bell.shift x))
    (by rw [map_sub, hL, hR, sub_mul])
    (by rw [map_sub, constantCoeff_subst_of_constantCoeff_eq_zero A
      (constantCoeff_bellWeightSeries A x), constantCoeff_exp, constantCoeff_egfA,
      Bell.complete_zero, sub_self])
  exact sub_eq_zero.mp hzero

end EGF

/-! ### The Lah column generating function -/

section Lah

variable (A : Type*) [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
/-- `1/(1-t) = 1 + t/(1-t)`. -/
theorem mkOne_eq_one_add_X_mul :
    (PowerSeries.mk 1 : A⟦X⟧) = 1 + X * PowerSeries.mk 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul]

omit [Algebra ℚ A] in
/-- `(1 - t)^2 · d/dt (t/(1-t)) = 1`. -/
theorem one_sub_X_sq_mul_derivative_X_mul_mkOne :
    ((1 : A⟦X⟧) - X) ^ 2 * d⁄dX A ((X : A⟦X⟧) * PowerSeries.mk 1) = 1 := by
  have hd : d⁄dX A (PowerSeries.mk 1 : A⟦X⟧) = PowerSeries.mk 1 * PowerSeries.mk 1 := by
    ext n
    rw [coeff_derivative, coeff_mk, Pi.one_apply, one_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [coeff_mk]
  rw [Derivation.leibniz, derivative_X, hd]
  have h1 : (PowerSeries.mk 1 : A⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one A
  calc ((1 : A⟦X⟧) - X) ^ 2 *
        ((X : A⟦X⟧) • (PowerSeries.mk 1 * PowerSeries.mk 1) + (PowerSeries.mk 1 : A⟦X⟧) • (1 : A⟦X⟧))
      = ((PowerSeries.mk 1 : A⟦X⟧) * (1 - X)) * ((PowerSeries.mk 1 : A⟦X⟧) * (1 - X)) * X
          + ((PowerSeries.mk 1 : A⟦X⟧) * (1 - X)) * (1 - X) := by
        simp only [smul_eq_mul]
        ring
    _ = 1 := by
        rw [h1]
        ring

/-- The first-order equation satisfied by the Lah column series:
`(1 - t) · d/dt (∑_n (k+1)! L(n,k+1) t^n/n!) = (k+1) · (∑_n (k+1)! L(n,k+1) t^n/n! + ∑_n k! L(n,k) t^n/n!)`. -/
theorem one_sub_X_mul_derivative_egf_lahNumber (k : ℕ) :
    (1 - X) * d⁄dX A (egf A fun n => (k + 1).factorial * lahNumber n (k + 1)) =
      ((k + 1 : ℕ) : A⟦X⟧) * (egf A (fun n => (k + 1).factorial * lahNumber n (k + 1))
        + egf A fun n => k.factorial * lahNumber n k) := by
  ext n
  have hcast : ∀ m : ℕ, ((m : A) + 1) = algebraMap ℚ A ((m : ℚ) + 1) := by
    intro m
    simp
  have hk : ((k + 1 : ℕ) : A) = algebraMap ℚ A ((k + 1 : ℕ) : ℚ) := by simp
  rw [sub_mul, one_mul, map_sub, ← map_natCast (C : A →+* A⟦X⟧) (k + 1), coeff_C_mul, hk,
    map_add, coeff_egf, coeff_egf, coeff_derivative, coeff_egf, hcast]
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, sub_zero, ← map_mul, ← map_add, ← map_mul]
    congr 1
    rw [lahNumber_succ_succ, Nat.factorial_succ k]
    push_cast
    ring
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_egf, hcast, ← map_mul, ← map_mul, ← map_sub,
      ← map_add, ← map_mul]
    congr 1
    rw [lahNumber_succ_succ, Nat.factorial_succ (n + 1), Nat.factorial_succ k]
    have h1 : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    try ring

omit [Algebra ℚ A] in
/-- `(1 - t) · d/dt (t/(1-t))^(k+1) = (k+1) ((t/(1-t))^(k+1) + (t/(1-t))^k)`. -/
theorem one_sub_X_mul_derivative_X_mul_mkOne_pow (k : ℕ) :
    (1 - X) * d⁄dX A (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1)) =
      ((k + 1 : ℕ) : A⟦X⟧) * (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1)
        + ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k) := by
  rw [derivative_pow, Nat.add_sub_cancel]
  have hsq := one_sub_X_sq_mul_derivative_X_mul_mkOne A
  have h1 : (PowerSeries.mk 1 : A⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one A
  have hm : (PowerSeries.mk 1 : A⟦X⟧) = 1 + X * PowerSeries.mk 1 := mkOne_eq_one_add_X_mul A
  calc (1 - X) * (((k + 1 : ℕ) : A⟦X⟧) * ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k *
          d⁄dX A ((X : A⟦X⟧) * PowerSeries.mk 1))
      = ((PowerSeries.mk 1 : A⟦X⟧) * (1 - X)) * ((1 - X) * (((k + 1 : ℕ) : A⟦X⟧) *
          ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k * d⁄dX A ((X : A⟦X⟧) * PowerSeries.mk 1))) := by
        rw [h1, one_mul]
    _ = ((k + 1 : ℕ) : A⟦X⟧) * ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k *
          (PowerSeries.mk 1 * (((1 : A⟦X⟧) - X) ^ 2 * d⁄dX A ((X : A⟦X⟧) * PowerSeries.mk 1))) := by
        ring
    _ = ((k + 1 : ℕ) : A⟦X⟧) * ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k * PowerSeries.mk 1 := by
        rw [hsq, mul_one]
    _ = ((k + 1 : ℕ) : A⟦X⟧) * ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k *
          (1 + X * PowerSeries.mk 1) := by
        rw [← hm]
    _ = _ := by ring

/-- **The Lah column generating function:**
`(t/(1-t))^k = ∑_n k! L(n,k) t^n/n!`. -/
theorem X_mul_mkOne_pow (k : ℕ) :
    ((X : A⟦X⟧) * PowerSeries.mk 1) ^ k = egf A fun n => k.factorial * lahNumber n k := by
  induction k with
  | zero =>
    ext n
    rw [pow_zero, coeff_one, coeff_egf]
    cases n with
    | zero => simp
    | succ n => simp
  | succ k ih =>
    -- the difference satisfies `D' = D · (k+1)/(1-t)`, and vanishes at `0`
    have hu := one_sub_X_mul_derivative_X_mul_mkOne_pow A k
    have hG := one_sub_X_mul_derivative_egf_lahNumber A k
    rw [← ih] at hG
    have h1 : (PowerSeries.mk 1 : A⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one A
    have key : d⁄dX A (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1)
          - egf A fun n => (k + 1).factorial * lahNumber n (k + 1))
        = (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1)
            - egf A fun n => (k + 1).factorial * lahNumber n (k + 1)) *
          (((k + 1 : ℕ) : A⟦X⟧) * PowerSeries.mk 1) := by
      calc d⁄dX A (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1)
              - egf A fun n => (k + 1).factorial * lahNumber n (k + 1))
          = ((PowerSeries.mk 1 : A⟦X⟧) * (1 - X)) *
              d⁄dX A (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1)
                - egf A fun n => (k + 1).factorial * lahNumber n (k + 1)) := by
            rw [h1, one_mul]
        _ = PowerSeries.mk 1 * ((1 - X) * d⁄dX A (((X : A⟦X⟧) * PowerSeries.mk 1) ^ (k + 1))
              - (1 - X) * d⁄dX A (egf A fun n => (k + 1).factorial * lahNumber n (k + 1))) := by
            rw [map_sub]
            ring
        _ = _ := by
            rw [hu, hG]
            ring
    have hzero := eq_zero_of_derivative_eq_mul A key
      (by rw [map_sub, map_pow, map_mul, constantCoeff_X, zero_mul, zero_pow (Nat.succ_ne_zero k),
        ← coeff_zero_eq_constantCoeff_apply, coeff_egf]
          simp)
    exact sub_eq_zero.mp hzero

end Lah

/-! ### Consequences: specializations and the Bell-number generating function -/

section Consequences

/-- Ring homomorphisms commute with the partial Bell polynomials. -/
theorem map_partialBell {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (x : ℕ → R) (n k : ℕ) : f (partialBell x n k) = partialBell (fun j => f (x j)) n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      cases k with
      | zero => simp
      | succ k => simp
    | succ n =>
      cases k with
      | zero => simp
      | succ k =>
        rw [partialBell_succ_succ, partialBell_succ_succ, map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [map_mul, map_mul, map_natCast, ih (n - i) (by omega) k]

/-- The weight series of `x_j = (j-1)!` is `-log(1-t)`. -/
theorem bellWeightSeries_factorial_pred :
    bellWeightSeries ℚ (fun j => ((j - 1).factorial : ℚ)) = negLogOneSub ℚ := by
  ext n
  rw [bellWeightSeries, coeff_egfA, coeff_negLogOneSub]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, Algebra.algebraMap_self,
      RingHom.id_apply]
    rw [Nat.factorial_succ]
    push_cast
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp

/-- From the column theorem over `ℚ`: `k! B_{n,k}(x)/n! = k! a_n/n!` identifies
`B_{n,k}(x)` with the coefficient sequence of `X(t)^k`. -/
theorem partialBell_eq_of_bellWeightSeries_pow_eq_egf (x : ℕ → ℚ) (a : ℕ → ℕ) (k : ℕ)
    (h : bellWeightSeries ℚ x ^ k = egf ℚ fun n => k.factorial * a n) (n : ℕ) :
    partialBell x n k = a n := by
  have hc := congrArg (coeff n) h
  rw [bellWeightSeries_pow, coeff_smul, coeff_egfA, coeff_egf, smul_eq_mul] at hc
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
  have hkn : (k.factorial : ℚ) * (1 / (n.factorial : ℚ)) ≠ 0 := by positivity
  apply mul_left_cancel₀ hkn
  calc (k.factorial : ℚ) * (1 / (n.factorial : ℚ)) * partialBell x n k
      = (k.factorial : ℚ) * (1 / (n.factorial : ℚ) * partialBell x n k) := by ring
    _ = (k.factorial : ℚ) * (a n : ℚ) / n.factorial := hc
    _ = (k.factorial : ℚ) * (1 / (n.factorial : ℚ)) * (a n : ℚ) := by ring

/-- **`B_{n,k}(0!,1!,2!,…) = c(n,k)`:** with `x_j = (j-1)!` (cycles), the partial
Bell polynomials are the unsigned Stirling numbers of the first kind. -/
theorem partialBell_factorial_pred (n k : ℕ) :
    partialBell (fun j => (j - 1).factorial) n k = Nat.stirlingFirst n k := by
  have hQ : partialBell (fun j => ((j - 1).factorial : ℚ)) n k = Nat.stirlingFirst n k :=
    partialBell_eq_of_bellWeightSeries_pow_eq_egf _ (fun n => Nat.stirlingFirst n k) k
      (by rw [bellWeightSeries_factorial_pred, negLogOneSub_pow]) n
  have hmap := map_partialBell (Nat.castRingHom ℚ) (fun j => (j - 1).factorial) n k
  simp only [Nat.coe_castRingHom] at hmap
  exact_mod_cast hmap.trans hQ

/-- The weight series of `x_j = j!` is `t/(1-t)`. -/
theorem bellWeightSeries_factorial :
    bellWeightSeries ℚ (fun j => (j.factorial : ℚ)) = X * PowerSeries.mk 1 := by
  ext n
  rw [bellWeightSeries, coeff_egfA]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_mk, Pi.one_apply]
    simp only [Nat.succ_ne_zero, if_false, Algebra.algebraMap_self, RingHom.id_apply]
    have hn : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    field_simp

/-- **`B_{n,k}(1!,2!,3!,…) = L(n,k)`:** with `x_j = j!` (linear orders), the partial
Bell polynomials are the Lah numbers. -/
theorem partialBell_factorial (n k : ℕ) :
    partialBell (fun j => j.factorial) n k = lahNumber n k := by
  have hQ : partialBell (fun j => (j.factorial : ℚ)) n k = lahNumber n k :=
    partialBell_eq_of_bellWeightSeries_pow_eq_egf _ (fun n => lahNumber n k) k
      (by rw [bellWeightSeries_factorial, X_mul_mkOne_pow]) n
  have hmap := map_partialBell (Nat.castRingHom ℚ) (fun j => j.factorial) n k
  simp only [Nat.coe_castRingHom] at hmap
  exact_mod_cast hmap.trans hQ

/-- The complete Bell polynomials at `x = (1,1,1,…)` are the Bell numbers. -/
theorem bell_complete_one (n : ℕ) : Bell.complete (fun _ => (1 : ℕ)) n = Nat.bell n := by
  rw [bell_complete_eq_sum_partialBell, bell_eq_sum_stirlingSecond]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact partialBell_one n k

/-- The weight series of `x = (1,1,1,…)` is `e^t - 1`. -/
theorem bellWeightSeries_one (A : Type*) [CommRing A] [Algebra ℚ A] :
    bellWeightSeries A (fun _ => 1) = exp A - 1 := by
  ext n
  rw [bellWeightSeries, coeff_egfA, map_sub, coeff_exp, coeff_one]
  cases n with
  | zero => simp
  | succ n => simp

/-- **The Bell-number generating function** `∑_n B(n) t^n/n! = exp(e^t - 1)`, as a
substitution of formal power series over any commutative `ℚ`-algebra. -/
theorem exp_subst_exp_sub_one (A : Type*) [CommRing A] [Algebra ℚ A] :
    (exp A).subst (exp A - 1) = egf A fun n => (Nat.bell n : ℚ) := by
  rw [← bellWeightSeries_one, exp_subst_bellWeightSeries, ← egfA_algebraMap]
  congr 1
  funext n
  rw [map_natCast, ← bell_complete_one, bell_complete_eq_sum_partialBell,
    bell_complete_eq_sum_partialBell, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := map_partialBell (Nat.castRingHom A) (fun _ => (1 : ℕ)) n k
  simp only [Nat.coe_castRingHom, Nat.cast_one] at h
  exact h.symm

end Consequences

end Fabius
