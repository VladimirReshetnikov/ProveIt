import FabiusFunction.ThueMorseIntegerLift

/-!
# The Catalan series behind the integer lift

Toward the algebraic equation `(1-z)³C(z)² + (1-z)²C(z) = z` for the
integral lift: the second difference of the lift is an alternating
Catalan–binomial series (the substituted Catalan generating function),
and products of such series collapse through a *diagonal Vandermonde*
identity.

* `sum_range_choose_mul_choose` — reusable **diagonal Vandermonde**
  (parallel summation): `∑_{i≤M} C(i,p)·C(M-i,q) = C(M+1, p+q+1)`.
* `sum_antidiagonal_choose_mul_choose` — the same identity in the
  `Finset.antidiagonal` shape Mathlib's Vandermonde lemmas use.
* `choose_second_difference` — Pascal's rule three times over:
  `C(n,k) - 2·C(n-1,k) + C(n-2,k) = C(n-2,k-2)` for `2 ≤ n`, `2 ≤ k`.
* `catalanSeriesDelta` — the coefficient sequence `h(m)` of the
  substituted alternating Catalan series `G(z/(1-z))`, with
  `h(0) = 1`.
* `integerLift_delta_bridge_all` — the bridge in **every** degree,
  `c(n) - 2c(n-1) + c(n-2) = h(n-1)` guarded at `n = 0`.  The guard
  is genuinely needed there and nowhere else: with `ℕ`-truncated
  subtraction the left side at `n = 0` is `0 - 2·0 + 0 = 0`, while
  `h(0 - 1) = h(0) = 1`.
* `integerLift_delta_bridge_of_one_le` — the unguarded bridge
  `c(n) - 2c(n-1) + c(n-2) = h(n-1)` for every `n ≥ 1`.
* `integerLift_delta_bridge` — its original `n ≥ 2` form.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Diagonal Vandermonde** (parallel summation), reusable:
`∑_{i=0}^{M} C(i,p)·C(M-i,q) = C(M+1, p+q+1)`. -/
theorem sum_range_choose_mul_choose (q M p : ℕ) :
    ∑ i ∈ range (M + 1), (i.choose p) * ((M - i).choose q) =
      (M + 1).choose (p + q + 1) := by
  induction q generalizing M with
  | zero =>
      -- hockey stick
      have hzero : ∀ i ∈ range (M + 1),
          (i.choose p) * ((M - i).choose 0) = i.choose p := by
        intro i _
        rw [Nat.choose_zero_right, Nat.mul_one]
      rw [Finset.sum_congr rfl hzero, Nat.add_zero]
      have hIcc : ∑ i ∈ range (M + 1), i.choose p =
          ∑ i ∈ Icc p M, i.choose p := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro i hi
          have := Finset.mem_Icc.mp hi
          exact Finset.mem_range.mpr (by omega)
        · intro i hi hnot
          have h1 := Finset.mem_range.mp hi
          have h2 : i < p := by
            by_contra hcon
            exact hnot (Finset.mem_Icc.mpr (by omega))
          exact Nat.choose_eq_zero_of_lt h2
      rw [hIcc, Nat.sum_Icc_choose]
  | succ q ihq =>
      induction M with
      | zero =>
          rw [Nat.choose_eq_zero_of_lt (by omega)]
          simp [Nat.choose_eq_zero_of_lt]
      | succ M ihM =>
          rw [Finset.sum_range_succ, Nat.sub_self,
            Nat.choose_eq_zero_of_lt (by omega : 0 < q + 1),
            Nat.mul_zero, Nat.add_zero]
          have hstep : ∀ i ∈ range (M + 1),
              (i.choose p) * ((M + 1 - i).choose (q + 1)) =
              (i.choose p) * ((M - i).choose q) +
                (i.choose p) * ((M - i).choose (q + 1)) := by
            intro i hi
            have h1 := Finset.mem_range.mp hi
            have h2 : M + 1 - i = (M - i) + 1 := by omega
            rw [h2, Nat.choose_succ_succ, Nat.mul_add]
          rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
            ihM, ihq M]
          have hP : (M + 1 + 1).choose (p + (q + 1) + 1) =
              (M + 1).choose (p + q + 1) + (M + 1).choose (p + (q + 1) + 1) := by
            have := Nat.choose_succ_succ (M + 1) (p + q + 1)
            rw [show p + (q + 1) + 1 = (p + q + 1) + 1 by ring]
            omega
          rw [hP]

/-- **Diagonal Vandermonde, antidiagonal form**: the same identity as
`sum_range_choose_mul_choose`, written over `Finset.antidiagonal M`,
which is the shape Mathlib states Vandermonde's identity in
(`Nat.add_choose_eq`).  Mathlib has no diagonal (parallel-summation)
Vandermonde of its own; this is the only generalisation available
cheaply. -/
theorem sum_antidiagonal_choose_mul_choose (q M p : ℕ) :
    ∑ ij ∈ Finset.antidiagonal M, (ij.1.choose p) * (ij.2.choose q) =
      (M + 1).choose (p + q + 1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_range_choose_mul_choose q M p

/-- **Second difference of a binomial column**: three applications of
Pascal's rule (`Nat.choose_eq_choose_pred_add`) collapse the second
difference in the *top* index to one doubly shifted binomial,
`C(n,k) - 2·C(n-1,k) + C(n-2,k) = C(n-2,k-2)` for `2 ≤ n`, `2 ≤ k`.
Stated over `ℤ`, where the subtractions are honest. -/
theorem choose_second_difference (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    (n.choose k : ℤ) - 2 * ((n - 1).choose k : ℤ) +
        ((n - 2).choose k : ℤ) =
      ((n - 2).choose (k - 2) : ℤ) := by
  have e1 : n - 1 - 1 = n - 2 := by omega
  have e2 : k - 1 - 1 = k - 2 := by omega
  have hp1 : n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k :=
    Nat.choose_eq_choose_pred_add (by omega) (by omega)
  have hp2 : (n - 1).choose k =
      (n - 1 - 1).choose (k - 1) + (n - 1 - 1).choose k :=
    Nat.choose_eq_choose_pred_add (by omega) (by omega)
  have hp3 : (n - 1).choose (k - 1) =
      (n - 1 - 1).choose (k - 1 - 1) + (n - 1 - 1).choose (k - 1) :=
    Nat.choose_eq_choose_pred_add (by omega) (by omega)
  rw [e1] at hp2
  rw [e1, e2] at hp3
  push_cast [hp1, hp2, hp3]
  ring

/-- The coefficient sequence `h(m)` of the substituted alternating
Catalan generating function `G(z/(1-z))`, `G(u) = ∑ (-1)^k·Cat(k)·u^k`:
`h(0) = 1` and `h(m) = ∑_{t=1}^m (-1)^t·Cat(t)·C(m-1, t-1)`. -/
def catalanSeriesDelta (m : ℕ) : ℤ :=
  if m = 0 then 1
  else ∑ t ∈ Icc 1 m, (-1) ^ t * (catalan t : ℤ) * ((m - 1).choose (t - 1) : ℤ)

/-- The substituted alternating Catalan coefficient in degree zero is `1`. -/
@[simp] theorem catalanSeriesDelta_zero : catalanSeriesDelta 0 = 1 := rfl

/-- The substituted alternating Catalan coefficient in degree one is `-1`. -/
theorem catalanSeriesDelta_one : catalanSeriesDelta 1 = -1 := by
  simp [catalanSeriesDelta]

/-- **The second-difference bridge, in all degrees**: the coefficients
of `(1-z)²C(z)` are the shifted substituted-Catalan values,
`c(n) - 2c(n-1) + c(n-2) = h(n-1)` — with the single exception of
`n = 0`, where `ℕ`-truncated subtraction makes the left side
`0 - 2·c(0) + c(0) = 0` while `h(0 - 1) = h(0) = 1`.  Hence the
`n = 0` guard, and no hypothesis. -/
theorem integerLift_delta_bridge_all (n : ℕ) :
    integerLift n - 2 * integerLift (n - 1) + integerLift (n - 2) =
      if n = 0 then 0 else catalanSeriesDelta (n - 1) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- the two small degrees, straight from the definitions
    interval_cases n
    · simp
    · rw [if_neg (by omega)]
      simp [integerLift_one, catalanSeriesDelta_zero]
  rw [if_neg (by omega)]
  -- extend all three sums to the common index range `Icc 1 n`
  have hext : ∀ r : ℕ, r ≤ n →
      integerLift r = ∑ k ∈ Icc 1 n,
        (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) * (r.choose k : ℤ) := by
    intro r hr
    rw [integerLift]
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hr) ?_
    intro k hk hknot
    have h1 := Finset.mem_Icc.mp hk
    have h2 : r < k := by
      by_contra hcon
      exact hknot (Finset.mem_Icc.mpr ⟨h1.1, by omega⟩)
    rw [Nat.choose_eq_zero_of_lt h2]
    push_cast
    ring
  rw [hext n le_rfl, hext (n - 1) (by omega), hext (n - 2) (by omega),
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  -- per-term double Pascal
  have hterm : ∀ k ∈ Icc 1 n,
      (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) * (n.choose k : ℤ) -
        2 * ((-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
          (((n - 1).choose k : ℕ) : ℤ)) +
        (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
          (((n - 2).choose k : ℕ) : ℤ) =
      (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
        (((n - 2).choose (k - 2) : ℕ) : ℤ) *
        (if k = 1 then 0 else 1) := by
    intro k hk
    have h1 := Finset.mem_Icc.mp hk
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl, mul_zero]
      rw [Nat.choose_one_right, Nat.choose_one_right, Nat.choose_one_right]
      have h1n : (((n - 1 : ℕ) : ℤ)) = (n : ℤ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
        ring
      have h2n : (((n - 2 : ℕ) : ℤ)) = (n : ℤ) - 2 := by
        push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
        ring
      rw [h1n, h2n]
      simp only [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, catalan_zero,
        Nat.cast_one, one_mul]
      ring
    · rw [if_neg hk1]
      have hnat := choose_second_difference n k (by omega) (by omega)
      calc (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) * (n.choose k : ℤ) -
            2 * ((-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
              (((n - 1).choose k : ℕ) : ℤ)) +
            (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
              (((n - 2).choose k : ℕ) : ℤ)
          = (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
              ((n.choose k : ℤ) - 2 * (((n - 1).choose k : ℕ) : ℤ) +
                (((n - 2).choose k : ℕ) : ℤ)) := by ring
        _ = (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
              (((n - 2).choose (k - 2) : ℕ) : ℤ) * 1 := by
            rw [hnat]
            ring
  rw [Finset.sum_congr rfl hterm]
  -- drop the vanishing `k = 1` term and reindex `t := k - 1`
  have h1mem : (1 : ℕ) ∈ Icc 1 n := Finset.mem_Icc.mpr (by omega)
  have herase : (Icc 1 n).erase 1 = Icc 2 n := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [← Finset.add_sum_erase _ _ h1mem, herase, if_pos rfl, mul_zero,
    zero_add]
  have hcong : ∀ k ∈ Icc 2 n,
      (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
        (((n - 2).choose (k - 2) : ℕ) : ℤ) * (if k = 1 then 0 else 1) =
      (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) *
        (((n - 2).choose (k - 2) : ℕ) : ℤ) := by
    intro k hk
    have := Finset.mem_Icc.mp hk
    rw [if_neg (by omega), mul_one]
  rw [Finset.sum_congr rfl hcong, catalanSeriesDelta,
    if_neg (by omega : ¬ n - 1 = 0)]
  refine Finset.sum_nbij' (fun k => k - 1) (fun t => t + 1)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr (by omega)
  · intro t ht
    have := Finset.mem_Icc.mp ht
    exact Finset.mem_Icc.mpr (by omega)
  · intro k hk
    have := Finset.mem_Icc.mp hk
    omega
  · intro t ht
    omega
  · intro k hk
    have := Finset.mem_Icc.mp hk
    rw [show n - 1 - 1 = n - 2 by omega, show k - 1 - 1 = k - 2 by omega]

/-- **The second-difference bridge for every positive degree**:
`c(n) - 2c(n-1) + c(n-2) = h(n-1)` for all `n ≥ 1`.  Only `n = 0` has
to be excluded; see `integerLift_delta_bridge_all`. -/
theorem integerLift_delta_bridge_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    integerLift n - 2 * integerLift (n - 1) + integerLift (n - 2) =
      catalanSeriesDelta (n - 1) := by
  have h := integerLift_delta_bridge_all n
  rw [if_neg (show ¬ n = 0 by omega)] at h
  exact h

/-- **The second-difference bridge**: the coefficients of `(1-z)²C(z)`
are the shifted substituted-Catalan values,
`c(n) - 2c(n-1) + c(n-2) = h(n-1)` for `n ≥ 2`. -/
theorem integerLift_delta_bridge (n : ℕ) (hn : 2 ≤ n) :
    integerLift n - 2 * integerLift (n - 1) + integerLift (n - 2) =
      catalanSeriesDelta (n - 1) :=
  integerLift_delta_bridge_of_one_le n (by omega)

end Fabius
