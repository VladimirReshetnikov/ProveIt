import FabiusFunction.GeometricUniformMomentPolynomial
import FabiusFunction.EvenZetaValues
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Degree.Monomial

/-!
# Sharp degree of the geometric-uniform moment polynomials

This file determines the top two coefficients of
`geometricUniformMomentPolynomial n`.  Reflecting in the already proved
triangular degree bound turns those coefficients into the constant and linear
coefficients of a finite product.  The resulting scalar recurrence is the
Bernoulli convolution.

The top coefficient is Mathlib's positive-convention Bernoulli number
`bernoulli' n / n!`.  For odd `n > 1` it vanishes, while the next coefficient
does not; this gives the exact parity-sensitive degree.

## Main declarations

* `coeff_geometricUniformMomentPolynomial_choose_two` gives the coefficient at
  the triangular upper bound.
* `coeff_geometricUniformMomentPolynomial_choose_two_sub_one` gives the next
  coefficient for `n >= 2`.
* `geometricUniformMomentPolynomial_natDegree_eq` gives the exact degree.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial

namespace Fabius

noncomputable section

private noncomputable def reversedGeometricUniformResidual (k n : ℕ) : ℚ[X] :=
  ∏ j ∈ Ico (k + 1) n, (X ^ j - 1)

private noncomputable def reversedGeometricUniformMomentPolynomial (n : ℕ) : ℚ[X] :=
  (geometricUniformMomentPolynomial n).reflect (n.choose 2)

private def geometricUniformLeadingValue (n : ℕ) : ℚ :=
  bernoulli' n / (n.factorial : ℚ)

private def geometricUniformSubleadingValue (n : ℕ) : ℚ :=
  -geometricUniformLeadingValue n + geometricUniformLeadingValue (n - 1) / 2

private theorem triangular_degree_split {k n : ℕ} (hkn : k < n) :
    k + ((∑ j ∈ Ico (k + 1) n, j) + k.choose 2) = n.choose 2 := by
  have hsplit :
      (∑ j ∈ range (k + 1), j) + ∑ j ∈ Ico (k + 1) n, j =
        ∑ j ∈ range n, j :=
    sum_range_add_sum_Ico (fun j => j) (by omega)
  have hkchoose : k + k.choose 2 = (k + 1).choose 2 := by
    rw [Nat.choose_succ_succ]
    simp
  have hsplit' :
      (k + 1).choose 2 + ∑ j ∈ Ico (k + 1) n, j = n.choose 2 := by
    simpa [sum_range_id, Nat.choose_two_right] using hsplit
  calc
    k + ((∑ j ∈ Ico (k + 1) n, j) + k.choose 2) =
        (k + k.choose 2) + ∑ j ∈ Ico (k + 1) n, j := by omega
    _ = (k + 1).choose 2 + ∑ j ∈ Ico (k + 1) n, j := by rw [hkchoose]
    _ = n.choose 2 := hsplit'

private theorem natDegree_geometricUniformResidual_le (k n : ℕ) :
    (∏ j ∈ Ico (k + 1) n, (1 - X ^ j : ℚ[X])).natDegree ≤
      ∑ j ∈ Ico (k + 1) n, j := by
  refine (natDegree_prod_le _ _).trans ?_
  refine sum_le_sum fun j _ => ?_
  exact (natDegree_sub_le _ _).trans
    (max_le (by simp) (natDegree_X_pow_le j))

private theorem reflect_finset_sum
    {R : Type*} [Semiring R] {s : Finset ℕ} (f : ℕ → R[X]) (N : ℕ) :
    (∑ i ∈ s, f i).reflect N = ∑ i ∈ s, (f i).reflect N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, reflect_add]

private theorem reflect_prod_one_sub_X_pow (s : Finset ℕ) :
    (∏ j ∈ s, (1 - X ^ j : ℚ[X])).reflect (∑ j ∈ s, j) =
      ∏ j ∈ s, (X ^ j - 1 : ℚ[X]) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haDegree : (1 - X ^ a : ℚ[X]).natDegree ≤ a :=
        (natDegree_sub_le _ _).trans
          (max_le (by simp) (natDegree_X_pow_le a))
      have hsDegree :
          (∏ j ∈ s, (1 - X ^ j : ℚ[X])).natDegree ≤ ∑ j ∈ s, j := by
        refine (natDegree_prod_le _ _).trans ?_
        refine sum_le_sum fun j _ => ?_
        exact (natDegree_sub_le _ _).trans
          (max_le (by simp) (natDegree_X_pow_le j))
      rw [sum_insert ha, prod_insert ha, prod_insert ha,
        reflect_mul _ _ haDegree hsDegree, ih]
      simp

private theorem reflect_geometricUniformMomentPolynomial_term
    {k n : ℕ} (hkn : k < n) :
    (C (((n - k + 1).factorial : ℚ)⁻¹) *
        (X ^ k *
          ((∏ j ∈ Ico (k + 1) n, (1 - X ^ j : ℚ[X])) *
            geometricUniformMomentPolynomial k))).reflect (n.choose 2) =
      C (((n - k + 1).factorial : ℚ)⁻¹) *
        (reversedGeometricUniformResidual k n *
          reversedGeometricUniformMomentPolynomial k) := by
  have hPk := geometricUniformMomentPolynomial_natDegree_le k
  have hres := natDegree_geometricUniformResidual_le k n
  have hinner :
      ((∏ j ∈ Ico (k + 1) n, (1 - X ^ j : ℚ[X])) *
          geometricUniformMomentPolynomial k).natDegree ≤
        (∑ j ∈ Ico (k + 1) n, j) + k.choose 2 :=
    natDegree_mul_le.trans (Nat.add_le_add hres hPk)
  rw [← triangular_degree_split hkn, reflect_C_mul,
    reflect_mul _ _ (natDegree_X_pow_le k) hinner,
    reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul,
    reflect_mul _ _ hres hPk, reflect_prod_one_sub_X_pow]
  rfl

private theorem reversedGeometricUniformMomentPolynomial_succ (n : ℕ) :
    reversedGeometricUniformMomentPolynomial (n + 1) =
      ∑ k ∈ range (n + 1),
        C (((n - k + 2).factorial : ℚ)⁻¹) *
          (reversedGeometricUniformResidual k (n + 1) *
            reversedGeometricUniformMomentPolynomial k) := by
  rw [reversedGeometricUniformMomentPolynomial,
    geometricUniformMomentPolynomial_succ, reflect_finset_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k < n + 1 := mem_range.mp hk
  have hindex : n + 1 - k + 1 = n - k + 2 := by omega
  simpa only [hindex] using
    (reflect_geometricUniformMomentPolynomial_term (n := n + 1) hkn)

private theorem coeff_zero_prod_X_pow_sub_one
    (s : Finset ℕ) (hs : ∀ j ∈ s, 0 < j) :
    (∏ j ∈ s, (X ^ j - 1 : ℚ[X])).coeff 0 = (-1 : ℚ) ^ #s := by
  rw [coeff_zero_prod]
  calc
    (∏ j ∈ s, (X ^ j - 1 : ℚ[X]).coeff 0) = ∏ _j ∈ s, (-1 : ℚ) := by
      apply prod_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := (hs j hj).ne'
      simp [coeff_X_pow, hj0.symm, coeff_one]
    _ = (-1 : ℚ) ^ #s := prod_const (-1 : ℚ)

private theorem coeff_zero_reversedGeometricUniformResidual
    {k n : ℕ} (hkn : k < n) :
    (reversedGeometricUniformResidual k n).coeff 0 =
      (-1 : ℚ) ^ (n - 1 - k) := by
  rw [reversedGeometricUniformResidual,
    coeff_zero_prod_X_pow_sub_one (Ico (k + 1) n)]
  · congr 1
    simp [Nat.card_Ico]
    omega
  · intro j hj
    have := (mem_Ico.mp hj).1
    omega

private theorem coeff_one_prod_X_pow_sub_one_eq_zero
    (s : Finset ℕ) (hs : ∀ j ∈ s, 2 ≤ j) :
    (∏ j ∈ s, (X ^ j - 1 : ℚ[X])).coeff 1 = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | @insert a s ha ih =>
      have ha2 : 2 ≤ a := hs a (mem_insert_self a s)
      have hs2 : ∀ j ∈ s, 2 ≤ j := fun j hj => hs j (mem_insert_of_mem hj)
      rw [prod_insert ha, mul_coeff_one, ih hs2]
      have hfactor : (X ^ a - 1 : ℚ[X]).coeff 1 = 0 := by
        rw [coeff_sub, coeff_X_pow, if_neg (by omega : 1 ≠ a), coeff_one]
        norm_num
      rw [hfactor]
      ring

private theorem coeff_one_reversedGeometricUniformResidual_of_pos
    {k n : ℕ} (hk : 0 < k) :
    (reversedGeometricUniformResidual k n).coeff 1 = 0 := by
  rw [reversedGeometricUniformResidual]
  apply coeff_one_prod_X_pow_sub_one_eq_zero
  intro j hj
  have := (mem_Ico.mp hj).1
  omega

private theorem coeff_one_reversedGeometricUniformResidual_zero
    {n : ℕ} (hn : 2 ≤ n) :
    (reversedGeometricUniformResidual 0 n).coeff 1 =
      (-1 : ℚ) ^ (n - 2) := by
  rw [reversedGeometricUniformResidual,
    Finset.prod_eq_prod_Ico_succ_bot (by omega : 1 < n)]
  rw [mul_coeff_one]
  have hhigh :
      (∏ j ∈ Ico 2 n, (X ^ j - 1 : ℚ[X])).coeff 1 = 0 := by
    apply coeff_one_prod_X_pow_sub_one_eq_zero
    intro j hj
    exact (mem_Ico.mp hj).1
  have hzero :
      (∏ j ∈ Ico 2 n, (X ^ j - 1 : ℚ[X])).coeff 0 =
        (-1 : ℚ) ^ (n - 2) := by
    rw [coeff_zero_prod_X_pow_sub_one (Ico 2 n)]
    · simp [Nat.card_Ico]
    · intro j hj
      exact lt_of_lt_of_le (by decide : 0 < 2) (mem_Ico.mp hj).1
  rw [hhigh, hzero]
  have hfactor0 : (X ^ 1 - 1 : ℚ[X]).coeff 0 = -1 := by
    rw [coeff_sub, coeff_X_pow, if_neg (by decide : ¬ 0 = 1), coeff_one]
    norm_num
  have hfactor1 : (X ^ 1 - 1 : ℚ[X]).coeff 1 = 1 := by
    rw [coeff_sub, coeff_X_pow_self, coeff_one]
    norm_num
  rw [hfactor0, hfactor1]
  ring

private theorem coeff_zero_reversedGeometricUniformMomentPolynomial_succ (n : ℕ) :
    (reversedGeometricUniformMomentPolynomial (n + 1)).coeff 0 =
      ∑ k ∈ range (n + 1),
        (((n - k + 2).factorial : ℚ)⁻¹) *
          ((-1 : ℚ) ^ (n - k) *
            (reversedGeometricUniformMomentPolynomial k).coeff 0) := by
  rw [reversedGeometricUniformMomentPolynomial_succ, finsetSum_coeff]
  apply sum_congr rfl
  intro k hk
  have hkn : k < n + 1 := mem_range.mp hk
  rw [coeff_C_mul, mul_coeff_zero,
    coeff_zero_reversedGeometricUniformResidual hkn]
  congr 3

private theorem bernoulli_factorial_convolution {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range N,
        _root_.bernoulli k /
          ((k.factorial : ℚ) * ((N - k + 1).factorial : ℚ)) =
      -_root_.bernoulli N / (N.factorial : ℚ) := by
  have hspec := bernoulli_spec' N
  rw [if_neg hN.ne'] at hspec
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hspec
  have hdiv := congrArg (fun x : ℚ => x / (N.factorial : ℚ)) hspec
  rw [sum_div, zero_div] at hdiv
  have hterm (k : ℕ) (hk : k ∈ range (N + 1)) :
      (((N.choose (N - k) : ℚ) / (N - k + 1) * _root_.bernoulli k) /
          (N.factorial : ℚ)) =
        _root_.bernoulli k /
          ((k.factorial : ℚ) * ((N - k + 1).factorial : ℚ)) := by
    have hkN : k ≤ N := by
      have := mem_range.mp hk
      omega
    have hden : ((N - k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hNfac : ((N.factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast N.factorial_ne_zero
    have hkfac : ((k.factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast k.factorial_ne_zero
    have hsubfac : (((N - k).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (N - k).factorial_ne_zero
    have hfac : (((N - k + 1).factorial : ℕ) : ℚ) =
        ((N - k + 1 : ℕ) : ℚ) * (((N - k).factorial : ℕ) : ℚ) := by
      rw [show N - k + 1 = (N - k).succ by omega, Nat.factorial_succ]
      push_cast
      rfl
    have hcast : ((N - k + 1 : ℕ) : ℚ) = (N : ℚ) - k + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hkN]
      push_cast
      ring
    rw [Nat.choose_symm hkN, Nat.cast_choose ℚ hkN, hfac, hcast]
    field_simp [hden, hNfac, hkfac, hsubfac]
  have hnormalized :
      (∑ k ∈ range (N + 1),
        _root_.bernoulli k /
          ((k.factorial : ℚ) * ((N - k + 1).factorial : ℚ))) = 0 := by
    calc
      _ = ∑ k ∈ range (N + 1),
          ((((k + (N - k)).choose (N - k) : ℚ) /
              (((N - k : ℕ) : ℚ) + 1) * _root_.bernoulli k) /
            (N.factorial : ℚ)) := by
              apply sum_congr rfl
              intro k hk
              have hkN : k ≤ N := by
                have := mem_range.mp hk
                omega
              have hsum : k + (N - k) = N := Nat.add_sub_of_le hkN
              have hcast : (((N - k : ℕ) : ℚ) + 1) =
                  ((N - k + 1 : ℕ) : ℚ) := by push_cast; rfl
              have hcast' : ((N - k + 1 : ℕ) : ℚ) = (N : ℚ) - k + 1 := by
                rw [Nat.cast_add, Nat.cast_sub hkN]
                push_cast
                ring
              rw [hsum, hcast]
              rw [hcast']
              exact (hterm k hk).symm
      _ = 0 := hdiv
  rw [sum_range_succ] at hnormalized
  simp only [Nat.sub_self, zero_add, Nat.factorial_one, Nat.cast_one,
    mul_one] at hnormalized
  calc
    _ = -(_root_.bernoulli N / (N.factorial : ℚ)) :=
      eq_neg_of_add_eq_zero_left hnormalized
    _ = -_root_.bernoulli N / (N.factorial : ℚ) := by ring

private theorem geometricUniformLeadingValue_recurrence {N : ℕ} (hN : 0 < N) :
    geometricUniformLeadingValue N =
      ∑ k ∈ range N,
        (-1 : ℚ) ^ (N - 1 - k) /
            ((N - k + 1).factorial : ℚ) *
          geometricUniformLeadingValue k := by
  have hconv := bernoulli_factorial_convolution hN
  rw [geometricUniformLeadingValue, bernoulli'_eq_bernoulli]
  calc
    (-1 : ℚ) ^ N * _root_.bernoulli N / (N.factorial : ℚ) =
        (-1 : ℚ) ^ (N - 1) *
          (-_root_.bernoulli N / (N.factorial : ℚ)) := by
            have hNsplit : N - 1 + 1 = N := Nat.sub_add_cancel hN
            rw [← hNsplit, pow_add]
            norm_num
            ring
    _ = (-1 : ℚ) ^ (N - 1) *
          (∑ k ∈ range N,
            _root_.bernoulli k /
              ((k.factorial : ℚ) * ((N - k + 1).factorial : ℚ))) := by
            rw [hconv]
    _ = ∑ k ∈ range N,
          (-1 : ℚ) ^ (N - 1 - k) /
              ((N - k + 1).factorial : ℚ) *
            geometricUniformLeadingValue k := by
            rw [mul_sum]
            apply sum_congr rfl
            intro k hk
            have hklt : k < N := mem_range.mp hk
            have hpow :
                (-1 : ℚ) ^ (N - 1 - k) * (-1 : ℚ) ^ k =
                  (-1 : ℚ) ^ (N - 1) := by
              rw [← pow_add]
              congr 2
              omega
            rw [geometricUniformLeadingValue, bernoulli'_eq_bernoulli, ← hpow]
            simp only [div_eq_mul_inv]
            ring

private theorem coeff_zero_reversedGeometricUniformMomentPolynomial (n : ℕ) :
    (reversedGeometricUniformMomentPolynomial n).coeff 0 =
      geometricUniformLeadingValue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [reversedGeometricUniformMomentPolynomial,
          geometricUniformLeadingValue]
      | succ n =>
          rw [coeff_zero_reversedGeometricUniformMomentPolynomial_succ,
            geometricUniformLeadingValue_recurrence (by omega : 0 < n + 1)]
          apply sum_congr rfl
          intro k hk
          rw [ih k (mem_range.mp hk)]
          have hklt : k < n + 1 := mem_range.mp hk
          have hfac : n - k + 2 = n + 1 - k + 1 := by omega
          have hsign : n - k = n + 1 - 1 - k := by omega
          rw [hfac, hsign]
          simp only [div_eq_mul_inv]
          ring

/-- The coefficient at the triangular degree bound is
`bernoulli' n / n!` (equivalently `(-1)^n B_n / n!`). -/
theorem coeff_geometricUniformMomentPolynomial_choose_two (n : ℕ) :
    (geometricUniformMomentPolynomial n).coeff (n.choose 2) =
      bernoulli' n / (n.factorial : ℚ) := by
  calc
    (geometricUniformMomentPolynomial n).coeff (n.choose 2) =
        (reversedGeometricUniformMomentPolynomial n).coeff 0 := by
          simp [reversedGeometricUniformMomentPolynomial]
    _ = geometricUniformLeadingValue n :=
      coeff_zero_reversedGeometricUniformMomentPolynomial n
    _ = bernoulli' n / (n.factorial : ℚ) := rfl

private theorem coeff_one_reversedGeometricUniformMomentPolynomial_succ
    {n : ℕ} (hn : 1 ≤ n) :
    (reversedGeometricUniformMomentPolynomial (n + 1)).coeff 1 =
      (((n + 2).factorial : ℚ)⁻¹) * (-1 : ℚ) ^ (n - 1) +
        ∑ k ∈ Ico 1 (n + 1),
          (((n - k + 2).factorial : ℚ)⁻¹) *
            ((-1 : ℚ) ^ (n - k) *
              (reversedGeometricUniformMomentPolynomial k).coeff 1) := by
  let f : ℕ → ℚ := fun k =>
    (C (((n - k + 2).factorial : ℚ)⁻¹) *
      (reversedGeometricUniformResidual k (n + 1) *
        reversedGeometricUniformMomentPolynomial k)).coeff 1
  calc
    (reversedGeometricUniformMomentPolynomial (n + 1)).coeff 1 =
        ∑ k ∈ range (n + 1), f k := by
          rw [reversedGeometricUniformMomentPolynomial_succ, finsetSum_coeff]
    _ = (∑ k ∈ range 1, f k) + ∑ k ∈ Ico 1 (n + 1), f k :=
      (sum_range_add_sum_Ico f (by omega)).symm
    _ = f 0 + ∑ k ∈ Ico 1 (n + 1), f k := by simp
    _ = (((n + 2).factorial : ℚ)⁻¹) * (-1 : ℚ) ^ (n - 1) +
        ∑ k ∈ Ico 1 (n + 1),
          (((n - k + 2).factorial : ℚ)⁻¹) *
            ((-1 : ℚ) ^ (n - k) *
              (reversedGeometricUniformMomentPolynomial k).coeff 1) := by
      congr 1
      · rw [show f 0 =
            (C (((n - 0 + 2).factorial : ℚ)⁻¹) *
              (reversedGeometricUniformResidual 0 (n + 1) *
                reversedGeometricUniformMomentPolynomial 0)).coeff 1 from rfl,
          coeff_C_mul, mul_coeff_one,
          coeff_one_reversedGeometricUniformResidual_zero (by omega : 2 ≤ n + 1)]
        simp [reversedGeometricUniformMomentPolynomial,
          geometricUniformMomentPolynomial_zero, coeff_one]
      · apply sum_congr rfl
        intro k hk
        have hkpos : 0 < k := (mem_Ico.mp hk).1
        have hklt : k < n + 1 := (mem_Ico.mp hk).2
        rw [show f k =
              (C (((n - k + 2).factorial : ℚ)⁻¹) *
                (reversedGeometricUniformResidual k (n + 1) *
                  reversedGeometricUniformMomentPolynomial k)).coeff 1 from rfl,
            coeff_C_mul, mul_coeff_one,
            coeff_one_reversedGeometricUniformResidual_of_pos hkpos,
            coeff_zero_reversedGeometricUniformResidual hklt]
        simp only [zero_mul, add_zero]
        congr 3

private theorem geometricUniformSubleadingValue_recurrence
    {N : ℕ} (hN : 2 ≤ N) :
    geometricUniformSubleadingValue N =
      (-1 : ℚ) ^ (N - 2) / ((N + 1).factorial : ℚ) +
        ∑ k ∈ Ico 1 N,
          (-1 : ℚ) ^ (N - 1 - k) /
              ((N - k + 1).factorial : ℚ) *
            geometricUniformSubleadingValue k := by
  let c : ℕ → ℚ := fun k =>
    (-1 : ℚ) ^ (N - 1 - k) /
      ((N - k + 1).factorial : ℚ)
  have haN := geometricUniformLeadingValue_recurrence (N := N) (by omega)
  have haPrev := geometricUniformLeadingValue_recurrence (N := N - 1) (by omega)
  have ha0 : geometricUniformLeadingValue 0 = 1 := by
    norm_num [geometricUniformLeadingValue]
  have hsumA :
      ∑ k ∈ Ico 1 N, c k * geometricUniformLeadingValue k =
        geometricUniformLeadingValue N - c 0 := by
    have hsplit := sum_range_add_sum_Ico
      (fun k => c k * geometricUniformLeadingValue k) (by omega : 1 ≤ N)
    have hfull :
        c 0 + ∑ k ∈ Ico 1 N, c k * geometricUniformLeadingValue k =
          geometricUniformLeadingValue N := by
      calc
        _ = (∑ k ∈ range 1, c k * geometricUniformLeadingValue k) +
              ∑ k ∈ Ico 1 N, c k * geometricUniformLeadingValue k := by
                simp [ha0]
        _ = ∑ k ∈ range N, c k * geometricUniformLeadingValue k := hsplit
        _ = geometricUniformLeadingValue N := by simpa only [c] using haN.symm
    linear_combination hfull
  have hsumPrev :
      ∑ k ∈ Ico 1 N, c k * geometricUniformLeadingValue (k - 1) =
        geometricUniformLeadingValue (N - 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [haPrev]
    apply sum_congr rfl
    intro k hk
    have hklt : k < N - 1 := mem_range.mp hk
    simp only [c]
    have hlead : 1 + k - 1 = k := by omega
    have hsign : N - 1 - (1 + k) = N - 1 - 1 - k := by omega
    have hfac : N - (1 + k) + 1 = N - 1 - k + 1 := by omega
    rw [hlead, hsign, hfac]
  have hsumB :
      ∑ k ∈ Ico 1 N, c k * geometricUniformSubleadingValue k =
        -(∑ k ∈ Ico 1 N, c k * geometricUniformLeadingValue k) +
          (∑ k ∈ Ico 1 N,
            c k * geometricUniformLeadingValue (k - 1)) / 2 := by
    simp_rw [geometricUniformSubleadingValue]
    calc
      _ = ∑ k ∈ Ico 1 N,
          (- (c k * geometricUniformLeadingValue k) +
            (c k * geometricUniformLeadingValue (k - 1)) / 2) := by
              apply sum_congr rfl
              intro k _
              ring
      _ = _ := by
        rw [sum_add_distrib, sum_neg_distrib, sum_div]
  have hsign :
      (-1 : ℚ) ^ (N - 2) + (-1 : ℚ) ^ (N - 1) = 0 := by
    have hsplit : N - 2 + 1 = N - 1 := by omega
    rw [← hsplit, pow_add]
    norm_num
  rw [geometricUniformSubleadingValue, hsumB, hsumA, hsumPrev]
  simp only [c, Nat.sub_zero]
  have hden : (((N + 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (N + 1).factorial_ne_zero
  field_simp [hden]
  linarith [hsign]

private theorem coeff_one_reversedGeometricUniformMomentPolynomial
    {n : ℕ} (hn : 1 ≤ n) :
    (reversedGeometricUniformMomentPolynomial n).coeff 1 =
      geometricUniformSubleadingValue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · omega
      · norm_num [reversedGeometricUniformMomentPolynomial,
          geometricUniformMomentPolynomial_one,
          geometricUniformSubleadingValue, geometricUniformLeadingValue,
          coeff_one]
      · rw [coeff_one_reversedGeometricUniformMomentPolynomial_succ (by omega : 1 ≤ n + 1),
          geometricUniformSubleadingValue_recurrence (by omega : 2 ≤ n + 2)]
        congr 1
        · have hsign : n + 1 - 1 = n + 2 - 2 := by omega
          rw [hsign]
          simp only [div_eq_mul_inv]
          ring
        · apply sum_congr rfl
          intro k hk
          have hkpos : 1 ≤ k := (mem_Ico.mp hk).1
          have hklt : k < n + 2 := (mem_Ico.mp hk).2
          rw [ih k hklt hkpos]
          have hfac : n + 1 - k + 2 = n + 2 - k + 1 := by omega
          have hsign : n + 1 - k = n + 2 - 1 - k := by omega
          rw [hfac, hsign]
          simp only [div_eq_mul_inv]
          ring

/-- For `n >= 2`, the coefficient immediately below the triangular bound is
`-bernoulli' n / n! + bernoulli' (n-1) / (2 (n-1)!)`. -/
theorem coeff_geometricUniformMomentPolynomial_choose_two_sub_one
    {n : ℕ} (hn : 2 ≤ n) :
    (geometricUniformMomentPolynomial n).coeff (n.choose 2 - 1) =
      -(bernoulli' n / (n.factorial : ℚ)) +
        bernoulli' (n - 1) / (2 * ((n - 1).factorial : ℚ)) := by
  have htri : 1 ≤ n.choose 2 := Nat.choose_pos hn
  calc
    (geometricUniformMomentPolynomial n).coeff (n.choose 2 - 1) =
        (reversedGeometricUniformMomentPolynomial n).coeff 1 := by
          rw [reversedGeometricUniformMomentPolynomial, coeff_reflect,
            revAt_le htri]
    _ = geometricUniformSubleadingValue n :=
      coeff_one_reversedGeometricUniformMomentPolynomial (by omega)
    _ = -(bernoulli' n / (n.factorial : ℚ)) +
        bernoulli' (n - 1) / (2 * ((n - 1).factorial : ℚ)) := by
          simp only [geometricUniformSubleadingValue, geometricUniformLeadingValue]
          ring

private theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) :
    _root_.bernoulli (2 * k) ≠ 0 := by
  intro hzero
  have hz := evenZeta_eq_bernoulli hk
  rw [hzero] at hz
  simp at hz
  exact (ne_of_gt (evenZeta_pos hk)) hz

private theorem bernoulli'_ne_zero_of_even
    {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) : bernoulli' n ≠ 0 := by
  obtain ⟨k, rfl⟩ := (even_iff_exists_two_mul.mp hn)
  have hk : k ≠ 0 := by omega
  have hB := bernoulli_two_mul_ne_zero hk
  rwa [bernoulli_eq_bernoulli'_of_ne_one (by omega)] at hB

/-- The exact degree is the triangular bound for `n = 1` and even `n`, and
one below that bound for odd `n > 1`. -/
theorem geometricUniformMomentPolynomial_natDegree_eq (n : ℕ) :
    (geometricUniformMomentPolynomial n).natDegree =
      if n = 1 ∨ Even n then n.choose 2 else n.choose 2 - 1 := by
  by_cases hmain : n = 1 ∨ Even n
  · rw [if_pos hmain]
    rcases hmain with rfl | hnEven
    · simp [geometricUniformMomentPolynomial_one]
    · by_cases hn0 : n = 0
      · subst n
        simp [geometricUniformMomentPolynomial_zero]
      · apply natDegree_eq_of_le_of_coeff_ne_zero
          (geometricUniformMomentPolynomial_natDegree_le n)
        rw [coeff_geometricUniformMomentPolynomial_choose_two]
        exact div_ne_zero (bernoulli'_ne_zero_of_even hn0 hnEven)
          (by exact_mod_cast n.factorial_ne_zero)
  · rw [if_neg hmain]
    have hn1 : n ≠ 1 := fun h => hmain (Or.inl h)
    have hnEven : ¬Even n := fun h => hmain (Or.inr h)
    have hnOdd : Odd n := Nat.not_even_iff_odd.mp hnEven
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact hnEven (by simp)
    have hnlt : 1 < n := by omega
    have hn2 : 2 ≤ n := by omega
    have htop :
        (geometricUniformMomentPolynomial n).coeff (n.choose 2) = 0 := by
      rw [coeff_geometricUniformMomentPolynomial_choose_two,
        bernoulli'_eq_zero_of_odd hnOdd hnlt]
      simp
    apply natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_le_pred (geometricUniformMomentPolynomial_natDegree_le n) htop)
    rw [coeff_geometricUniformMomentPolynomial_choose_two_sub_one hn2,
      bernoulli'_eq_zero_of_odd hnOdd hnlt]
    simp only [zero_div, neg_zero, zero_add]
    have hpred0 : n - 1 ≠ 0 := by omega
    have hpredEven : Even (n - 1) := hnOdd.tsub_odd odd_one
    exact div_ne_zero (bernoulli'_ne_zero_of_even hpred0 hpredEven)
      (mul_ne_zero (by norm_num) (by exact_mod_cast (n - 1).factorial_ne_zero))

end

end Fabius
