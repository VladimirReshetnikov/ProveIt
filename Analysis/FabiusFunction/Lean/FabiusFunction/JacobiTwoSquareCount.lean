import FabiusFunction.PartitionDistinctOdd
import FabiusFunction.RamanujanOnePsiOne
import FabiusFunction.ThetaProductIdentities
import FabiusFunction.TwoSquareTheorem

/-!
# Jacobi's two-square theorem

This module closes the arithmetic core left parameterized in
`FabiusFunction.TwoSquareTheorem`.  The proof uses a compact specialization of
Ramanujan's bilateral `₁ψ₁` summation rather than rebuilding the divisor theory of
Gaussian integers.

Put `Q = q²`.  At `a = -1`, `b = -Q`, and `z = q`, the `₁ψ₁` summand is

`2 qⁿ / (1 + q²ⁿ)`.

It is even in the integer index, so the bilateral sum is
`1 + 4 ∑_{n ≥ 1} qⁿ/(1+q²ⁿ)`.  Expanding the denominator geometrically and
interchanging an absolutely convergent double series gives the odd Lambert series

`∑_{j ≥ 0} (-1)ʲ q²ʲ⁺¹/(1-q²ʲ⁺¹)`.

On the product side, the elementary identities
`(a;r)_∞(-a;r)_∞=(a²;r²)_∞` and
`(-r;r)_∞=(r;r²)_∞⁻¹` reduce Ramanujan's quotient to the square of
Jacobi's theta product.  Power-series coefficient uniqueness then proves
`r₂(n)=4 ∑_{d∣n} χ₄(d)` for every positive `n`.  Finally, the two
hypothesis-parameterized analytic theorems in `TwoSquareTheorem` are retained as
reusable kernels and instantiated here to give unconditional wrappers.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

private theorem qPochhammerInfIn_mul_neg_eq_sq {a r : ℂ} (hr : ‖r‖ < 1) :
    qPochhammerInfIn a r * qPochhammerInfIn (-a) r =
      qPochhammerInfIn (a ^ 2) (r ^ 2) := by
  have hr2 : ‖r ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hr (by norm_num)
  have h := (hasProd_qPochhammerInfIn a hr).mul (hasProd_qPochhammerInfIn (-a) hr)
  have h' : HasProd (fun n : ℕ => 1 - a ^ 2 * (r ^ 2) ^ n)
      (qPochhammerInfIn a r * qPochhammerInfIn (-a) r) := by
    refine h.congr_fun fun n => ?_
    show 1 - a ^ 2 * (r ^ 2) ^ n = (1 - a * r ^ n) * (1 - -a * r ^ n)
    rw [pow_two a, pow_two r, mul_pow]
    ring
  exact ((hasProd_qPochhammerInfIn (a ^ 2) hr2).unique h').symm

private theorem qPochhammerInfIn_odd_mul_neg_odd_mul_neg_even_eq_one
    {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q (q ^ 2) * qPochhammerInfIn (-q) (q ^ 2) *
        qPochhammerInfIn (-(q ^ 2)) (q ^ 2) = 1 := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hq4 : ‖(q ^ 2) ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq2 (by norm_num)
  have hmul := qPochhammerInfIn_mul_neg_eq_sq (a := q) hq2
  have hneg := qPochhammerInfIn_neg_self_eq hq2
  have hne : qPochhammerInfIn (q ^ 2) ((q ^ 2) ^ 2) ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hq4 hq2
  rw [hmul, hneg]
  exact mul_inv_cancel₀ hne

private theorem one_add_pow_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) :
    1 + Q ^ n ≠ 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num
  · have hpow : ‖Q ^ n‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg Q) hQ hn
    intro hzero
    have heq : Q ^ n = -1 := by linear_combination hzero
    rw [heq, norm_neg, norm_one] at hpow
    exact (lt_irrefl 1 hpow).elim

private theorem finiteQPochhammerIn_neg_one_div_neg_base {Q : ℂ} (hQ : ‖Q‖ < 1)
    (n : ℕ) :
    finiteQPochhammerIn (-1) Q n / finiteQPochhammerIn (-Q) Q n =
      2 / (1 + Q ^ n) := by
  have hBinf : qPochhammerInfIn (-Q) Q ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hQ (by simpa using hQ)
  have hB : finiteQPochhammerIn (-Q) Q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (-Q) hQ hBinf n
  have hfac : 1 + Q ^ n ≠ 0 := one_add_pow_ne_zero hQ n
  apply (div_eq_div_iff hB hfac).2
  calc
    finiteQPochhammerIn (-1) Q n * (1 + Q ^ n) =
        finiteQPochhammerIn (-1) Q (n + 1) := by
          rw [finiteQPochhammerIn_succ]
          ring
    _ = 2 * finiteQPochhammerIn (-Q) Q n := by
      rw [finiteQPochhammerIn_succ_shift]
      ring_nf

private theorem onePsiOneTerm_twoSquare_natCast {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q n =
      2 * (q ^ n / (1 + (q ^ 2) ^ n)) := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  rw [onePsiOneTerm, finiteQPochhammerZ_natCast, finiteQPochhammerZ_natCast,
    finiteQPochhammerIn_neg_one_div_neg_base hq2, zpow_natCast]
  ring

private theorem onePsiOneTerm_twoSquare_neg_natCast {q : ℂ} (hq : ‖q‖ < 1)
    (hq0 : q ≠ 0) (n : ℕ) :
    onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q (-n) =
      2 * (q ^ n / (1 + (q ^ 2) ^ n)) := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hq20 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hqn : q ^ n ≠ 0 := pow_ne_zero n hq0
  have hden : 1 + (q ^ 2) ^ n ≠ 0 := one_add_pow_ne_zero hq2 n
  rw [onePsiOneTerm,
    finiteQPochhammerZ_div_neg_natCast (a := (-1 : ℂ)) (b := -(q ^ 2))
      (q := q ^ 2) (by norm_num) (neg_ne_zero.mpr hq20) hq20,
    show (-(q ^ 2)) / (-1 : ℂ) = q ^ 2 by ring,
    show (q ^ 2) / (-(q ^ 2)) = (-1 : ℂ) by field_simp,
    show (q ^ 2) / (-1 : ℂ) = -(q ^ 2) by ring,
    finiteQPochhammerIn_neg_one_div_neg_base hq2, zpow_neg, zpow_natCast]
  field_simp [hqn, hden]
  rw [pow_two, mul_pow]
  ring

private theorem onePsiOneTerm_twoSquare_even {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    Function.Even (onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q) := by
  intro n
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [onePsiOneTerm_twoSquare_neg_natCast hq hq0,
      onePsiOneTerm_twoSquare_natCast hq]
  · rw [neg_neg, onePsiOneTerm_twoSquare_natCast hq,
      onePsiOneTerm_twoSquare_neg_natCast hq hq0]

private theorem summable_twoSquareLambertCells {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun p : ℕ × ℕ =>
      (-1 : ℂ) ^ p.1 * q ^ ((2 * p.1 + 1) * (p.2 + 1)) := by
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have hshift : Summable fun n : ℕ => ‖q‖ ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hgeom
  have hprod := hshift.mul_of_nonneg hgeom
    (fun n => pow_nonneg (norm_nonneg q) (n + 1))
    (fun n => pow_nonneg (norm_nonneg q) n)
  refine Summable.of_norm_bounded hprod ?_
  rintro ⟨j, n⟩
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hexp : j + 1 + n ≤ (2 * j + 1) * (n + 1) := by
    nlinarith [Nat.zero_le (j * (2 * n + 1))]
  calc
    ‖q‖ ^ ((2 * j + 1) * (n + 1)) ≤ ‖q‖ ^ (j + 1 + n) :=
      pow_le_pow_of_le_one (norm_nonneg q) hq.le hexp
    _ = ‖q‖ ^ (j + 1) * ‖q‖ ^ n := by rw [pow_add]

private theorem tsum_twoSquare_positive_eq_oddLambert {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1))) =
      ∑' j : ℕ, (-1 : ℂ) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
  let F : ℕ × ℕ → ℂ := fun p =>
    (-1 : ℂ) ^ p.1 * q ^ ((2 * p.1 + 1) * (p.2 + 1))
  have hF : Summable F := summable_twoSquareLambertCells hq
  have hrow : ∀ j : ℕ, HasSum (fun n : ℕ => F (j, n))
      ((-1 : ℂ) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1))) := by
    intro j
    have hr : ‖q ^ (2 * j + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
    have h := (hasSum_geometric_of_norm_lt_one hr).mul_left
      ((-1 : ℂ) ^ j * q ^ (2 * j + 1))
    refine h.congr_fun fun n => ?_
    dsimp [F]
    rw [pow_mul, pow_succ']
    ring
  have hcol : ∀ n : ℕ, HasSum (fun j : ℕ => F (j, n))
      (q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1))) := by
    intro n
    have hr : ‖-(q ^ 2) ^ (n + 1)‖ < 1 := by
      rw [norm_neg, norm_pow, norm_pow]
      have hq2 : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
      exact pow_lt_one₀ (pow_nonneg (norm_nonneg q) 2) hq2 (by omega)
    have h := (hasSum_geometric_of_norm_lt_one hr).mul_left (q ^ (n + 1))
    have hval : q ^ (n + 1) * (1 - -(q ^ 2) ^ (n + 1))⁻¹ =
        q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1)) := by
      rw [div_eq_mul_inv]
      congr 2
      ring
    rw [hval] at h
    refine h.congr_fun fun j => ?_
    dsimp [F]
    have hpow : q ^ ((2 * j + 1) * (n + 1)) =
        q ^ (n + 1) * ((q ^ 2) ^ (n + 1)) ^ j := by
      rw [show (2 * j + 1) * (n + 1) = (n + 1) + (2 * (n + 1)) * j by ring,
        pow_add, pow_mul, pow_mul]
    rw [hpow, neg_pow]
    ring
  have hF' : Summable (Function.uncurry fun n j => F (j, n)) := by
    refine hF.prod_symm.congr ?_
    rintro ⟨n, j⟩
    rfl
  have hcomm : (∑' j : ℕ, ∑' n : ℕ, F (j, n)) =
      ∑' n : ℕ, ∑' j : ℕ, F (j, n) := Summable.tsum_comm hF'
  calc
    (∑' n : ℕ, q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1))) =
        ∑' n : ℕ, ∑' j : ℕ, F (j, n) := by
          refine tsum_congr fun n => (hcol n).tsum_eq.symm
    _ = ∑' j : ℕ, ∑' n : ℕ, F (j, n) := hcomm.symm
    _ = ∑' j : ℕ,
        (-1 : ℂ) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
          refine tsum_congr fun j => (hrow j).tsum_eq

private theorem tsum_onePsiOne_twoSquare_eq {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hsum : Summable (onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q)) :
    (∑' n : ℤ, onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q n) =
      1 + 4 * ∑' n : ℕ, q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1)) := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (onePsiOneTerm_twoSquare_even hq hq0) hsum]
  have hzero := onePsiOneTerm_twoSquare_natCast hq 0
  norm_num at hzero
  rw [hzero, nsmul_eq_mul]
  have hpnat :
      (∑' n : ℕ+, onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q (n : ℤ)) =
        ∑' n : ℕ,
          onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q ((n + 1 : ℕ) : ℤ) := by
    simpa using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q (n : ℤ)))
  rw [hpnat]
  calc
    1 + 2 * ∑' n : ℕ,
        onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q (n + 1) =
        1 + 2 * ∑' n : ℕ,
          2 * (q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1))) := by
            congr 2
            refine tsum_congr fun n => onePsiOneTerm_twoSquare_natCast hq (n + 1)
    _ = 1 + 4 * ∑' n : ℕ, q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1)) := by
      rw [tsum_mul_left]
      ring

private theorem sqExponent_eq_natAbs_sq' (m : ℤ) : sqExponent m = m.natAbs ^ 2 := by
  have h : ((sqExponent m : ℕ) : ℤ) = ((m.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [sqExponent_cast, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  exact_mod_cast h

private theorem theta_sq_eq_odd_lambert_complex_of_ne_zero {q : ℂ} (hq : ‖q‖ < 1)
    (hq0 : q ≠ 0) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2 =
      1 + 4 * ∑' j : ℕ,
        (-1 : ℂ) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hq20 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hneg : qPochhammerInfIn (-(q ^ 2)) (q ^ 2) ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hq2 (by simpa using hq2)
  have hba : (-(q ^ 2)) / (-1 : ℂ) = q ^ 2 := by ring
  have hQa : (q ^ 2) / (-1 : ℂ) = -(q ^ 2) := by ring
  have hQnegq : (q ^ 2) / (-q) = -q := by
    field_simp
  have hbnegq : (-(q ^ 2)) / (-q) = q := by
    field_simp
  have hbz : ‖(-(q ^ 2)) / (-1 : ℂ)‖ < ‖q‖ := by
    rw [hba, norm_pow]
    have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    nlinarith
  have hQa_nonzero : qPochhammerInfIn ((q ^ 2) / (-1 : ℂ)) (q ^ 2) ≠ 0 := by
    rw [hQa]
    exact hneg
  have hpsi := hasSum_onePsiOne (a := (-1 : ℂ)) (b := -(q ^ 2))
    (q := q ^ 2) (z := q) hq2 hq20 (by norm_num) hQa_nonzero hneg hbz hq
  rw [neg_one_mul, hba, hQa, hQnegq, hbnegq] at hpsi
  let A := qPochhammerInfIn (q ^ 2) (q ^ 2)
  let B := qPochhammerInfIn (-q) (q ^ 2)
  let C := qPochhammerInfIn (-(q ^ 2)) (q ^ 2)
  let D := qPochhammerInfIn q (q ^ 2)
  have hB : B ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hq2 (by simpa [B] using hq)
  have hone : D * B * C = 1 := by
    simpa [B, C, D] using qPochhammerInfIn_odd_mul_neg_odd_mul_neg_even_eq_one hq
  have hCB : C * D = B⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc
      B * (C * D) = D * B * C := by ring
      _ = 1 := hone
  have hden : C * C * D * D = (B⁻¹) ^ 2 := by
    rw [show C * C * D * D = (C * D) ^ 2 by ring, hCB]
  have hval : A * A * B * B / (C * C * D * D) = (A * B ^ 2) ^ 2 := by
    rw [hden]
    field_simp [hB]
  change HasSum (onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q)
    (A * A * B * B / (C * C * D * D)) at hpsi
  rw [hval] at hpsi
  have htheta : (∑' m : ℤ, q ^ (m.natAbs ^ 2)) = A * B ^ 2 := by
    rw [← (hasSum_pow_sqExponent hq hq0).tsum_eq]
    exact tsum_congr fun m => by rw [sqExponent_eq_natAbs_sq']
  calc
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2 = (A * B ^ 2) ^ 2 := by rw [htheta]
    _ = ∑' n : ℤ, onePsiOneTerm (-1) (-(q ^ 2)) (q ^ 2) q n := hpsi.tsum_eq.symm
    _ = 1 + 4 * ∑' n : ℕ, q ^ (n + 1) / (1 + (q ^ 2) ^ (n + 1)) :=
      tsum_onePsiOne_twoSquare_eq hq hq0 hpsi.summable
    _ = 1 + 4 * ∑' j : ℕ,
        (-1 : ℂ) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
      rw [tsum_twoSquare_positive_eq_oddLambert hq]

private theorem theta_sq_eq_odd_lambert_complex {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2 =
      1 + 4 * ∑' j : ℕ,
        (-1 : ℂ) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have hsum := hasSum_sumSqRep (𝕜 := ℂ) (q := 0) (by norm_num) 2
    have hone : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 1 :=
      hasSum_ite_eq 0 1
    have hone' : HasSum (fun n : ℕ => (sumSqRep 2 n : ℂ) * 0 ^ n) 1 := by
      refine hone.congr_fun fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [sumSqRep_two_zero]
      · simp [hn]
    have htheta := hsum.unique hone'
    simpa using htheta
  · exact theta_sq_eq_odd_lambert_complex_of_ne_zero hq hq0

private theorem theta_sq_eq_chi4_lambert_complex {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2 =
      1 + 4 * ∑' d : ℕ,
        ((chi4 d : ℤ) : ℂ) * q ^ d / (1 - q ^ d) := by
  rw [theta_sq_eq_odd_lambert_complex hq, tsum_chi4_lambert_eq_tsum_odd]

private theorem twoSquare_coefficients :
    (fun n : ℕ => ((sumSqRep 2 n : ℕ) : ℂ)) =
      fun n : ℕ => if n = 0 then 1 else 4 * ((twoSquareDivisorSum n : ℤ) : ℂ) := by
  refine eq_of_hasSum_pow_eq (f := fun q : ℂ =>
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2) (zero_lt_one : (0 : ℝ) < 1)
      (fun q hq => hasSum_sumSqRep hq 2) ?_
  intro q hq
  have h4 := (hasSum_twoSquareDivisorSum_lambert (𝕜 := ℂ) hq).mul_left (4 : ℂ)
  have h1 : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 1 := hasSum_ite_eq 0 1
  have hsum := h1.add h4
  have hcongr : HasSum
      (fun n : ℕ => (if n = 0 then 1 else 4 * ((twoSquareDivisorSum n : ℤ) : ℂ)) * q ^ n)
      (1 + 4 * ∑' d : ℕ, ((chi4 d : ℤ) : ℂ) * q ^ d / (1 - q ^ d)) := by
    refine hsum.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [twoSquareDivisorSum_zero]
    · simp only [if_neg hn]
      ring
  rw [← theta_sq_eq_chi4_lambert_complex hq] at hcongr
  exact hcongr

/-- **Jacobi's two-square theorem** (`qg:thm-two-square`): for every positive `n`, the number
of ordered signed representations of `n` as two squares is four times the `χ₄` divisor sum. -/
theorem sumSqRep_two_eq_four_mul_twoSquareDivisorSum {n : ℕ} (hn : n ≠ 0) :
    (sumSqRep 2 n : ℤ) = 4 * twoSquareDivisorSum n := by
  have h := congrFun twoSquare_coefficients n
  rw [if_neg hn] at h
  exact_mod_cast h

/-- The product form of Jacobi's two-square theorem: when every prime `3 (mod 4)` has even
valuation, the representation count is `4` times the product of `v_p(n)+1` over primes
`1 (mod 4)`. -/
theorem sumSqRep_two_eq_four_mul_prod {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p % 4 = 3 → Even (n.factorization p)) :
    (sumSqRep 2 n : ℤ) =
      4 * ∏ p ∈ Finset.filter (fun p : ℕ => p % 4 = 1) n.primeFactors,
        ((n.factorization p : ℤ) + 1) := by
  rw [sumSqRep_two_eq_four_mul_twoSquareDivisorSum hn,
    twoSquareDivisorSum_eq_prod hn h]

section Lambert

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The first equality of `qg:cor-two-square-lambert`, unconditionally.**  For every complete
normed field and `‖q‖ < 1`, the square of the theta series is the `χ₄` Lambert series. -/
theorem theta_sq_eq_chi4_lambert {q : 𝕜} (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2 =
      1 + 4 * ∑' d : ℕ, ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d) :=
  hasSum_theta_sq_lambert
    (fun _ hn => sumSqRep_two_eq_four_mul_twoSquareDivisorSum hn) hq

/-- **`qg:cor-two-square-lambert`, unconditionally and in full.**  For every complete normed
field and `‖q‖ < 1`, the square of the theta series is the alternating odd Lambert series. -/
theorem theta_sq_eq_odd_lambert {q : 𝕜} (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2 =
      1 + 4 * ∑' j : ℕ,
        (-1 : 𝕜) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) :=
  theta_sq_eq_lambert_odd
    (fun _ hn => sumSqRep_two_eq_four_mul_twoSquareDivisorSum hn) hq

end Lambert

end Fabius
