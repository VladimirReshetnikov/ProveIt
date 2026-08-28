import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Leading jets of a factored function

If a one-variable function has the form `z ^ n * U z` near a point, then
the monomial selects a single term from every Leibniz sum.  At the origin,
the `k`-th derivative is zero for `k < n`; for `k = n + r` it is
`choose (n + r) n * n!` times the `r`-th derivative of `U`.  Only the
corresponding finite differentiability of the residual factor is needed.

The foundational result is vector-valued and division-free.  In particular,
it does not require characteristic zero, completeness, or analyticity.  The
scalar germ corollaries are the common local engine behind exact zero jets.
They are independent of the Fabius function and complex analysis.

* `iteratedDeriv_pow_smul_zero_eq_ite` computes every jet of a vector-valued
  factored function.
* `iteratedDeriv_pow_smul_zero_add` and
  `iteratedDeriv_pow_mul_zero_add` give the division-free `n + r` forms.
* `iteratedDeriv_eq_choose_factorial_mul_of_eventuallyEq_pow_mul` and its
  arbitrary-center companion apply the computation to local factorizations.
* `iteratedDeriv_eq_ite_of_eventuallyEq_sub_pow_smul` and
  `iteratedDeriv_eq_choose_factorial_smul_of_eventuallyEq_sub_pow_smul`
  retain the vector-valued statement at an arbitrary center.
* `iteratedDeriv_pow_mul_zero` and
  `iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul` retain the leading
  `r = 0` forms as convenient compatibility lemmas.
-/

set_option autoImplicit false

namespace Fabius

open Filter

/-- **All jets of a monomial times a vector-valued function.**  At the
origin, the monomial `z ^ n` kills every derivative below order `n` and
selects exactly the `i = n` term of the Leibniz sum thereafter.

This is deliberately stated without factorial division.  It remains valid
over normed fields of positive characteristic, where the displayed scalar
may vanish. -/
theorem iteratedDeriv_pow_smul_zero_eq_ite
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (n k : ℕ) {U : 𝕜 → E} (hU : ContDiffAt 𝕜 k U 0) :
    iteratedDeriv k (fun z : 𝕜 => z ^ n • U z) 0 =
      if n ≤ k then
        ((k.choose n : 𝕜) * (n.factorial : 𝕜)) •
          iteratedDeriv (k - n) U 0
      else 0 := by
  change iteratedDeriv k ((fun z : 𝕜 => z ^ n) • U) 0 = _
  have hpow : ContDiffAt 𝕜 k (fun z : 𝕜 => z ^ n) 0 := by
    exact contDiffAt_id.pow n
  have hleibniz :
      iteratedDeriv k ((fun z : 𝕜 => z ^ n) • U) 0 =
        ∑ i ∈ Finset.range (k + 1),
          k.choose i •
            (iteratedDeriv i (fun z : 𝕜 => z ^ n) 0 •
              iteratedDeriv (k - i) U 0) := by
    simpa only [iteratedDerivWithin_univ] using
      (iteratedDerivWithin_smul
        (𝕜 := 𝕜) (𝔸 := 𝕜) (F := E) (n := k)
        (f := fun z : 𝕜 => z ^ n) (g := U)
        (s := Set.univ) (x := (0 : 𝕜))
        (Set.mem_univ (0 : 𝕜)) uniqueDiffOn_univ
        hpow.contDiffWithinAt hU.contDiffWithinAt)
  rw [hleibniz]
  by_cases hnk : n ≤ k
  · rw [if_pos hnk]
    have hnmem : n ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hnk)
    rw [Finset.sum_eq_single_of_mem n hnmem]
    · simp only [iteratedDeriv_fun_pow_zero, if_true]
      rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
    · intro i _hi hin
      simp only [iteratedDeriv_fun_pow_zero, if_neg hin, Nat.cast_zero,
        zero_smul, smul_zero]
  · rw [if_neg hnk]
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≤ k :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hin : i ≠ n :=
      ne_of_lt (hik.trans_lt (Nat.lt_of_not_ge hnk))
    simp only [iteratedDeriv_fun_pow_zero, if_neg hin, Nat.cast_zero,
      zero_smul, smul_zero]

/-- **Division-free higher-jet form.**  The `(n+r)`-th derivative of
`z ^ n • U z` at zero is `choose (n+r) n * n!` times the `r`-th derivative
of `U`. -/
theorem iteratedDeriv_pow_smul_zero_add
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (n r : ℕ) {U : 𝕜 → E} (hU : ContDiffAt 𝕜 (n + r) U 0) :
    iteratedDeriv (n + r) (fun z : 𝕜 => z ^ n • U z) 0 =
      (((n + r).choose n : 𝕜) * (n.factorial : 𝕜)) •
        iteratedDeriv r U 0 := by
  simpa only [if_pos (Nat.le_add_right n r), Nat.add_sub_cancel_left] using
    iteratedDeriv_pow_smul_zero_eq_ite n (n + r) hU

/-- Scalar multiplication form of `iteratedDeriv_pow_smul_zero_add`. -/
theorem iteratedDeriv_pow_mul_zero_add
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (n r : ℕ) {U : 𝕜 → 𝕜} (hU : ContDiffAt 𝕜 (n + r) U 0) :
    iteratedDeriv (n + r) (fun z : 𝕜 => z ^ n * U z) 0 =
      ((n + r).choose n : 𝕜) * (n.factorial : 𝕜) *
        iteratedDeriv r U 0 := by
  simpa only [smul_eq_mul] using
    iteratedDeriv_pow_smul_zero_add n r hU

/-- **All higher jets from a local factorization at zero.**  No regularity
hypothesis on `f` is needed beyond its agreement with `z ^ n * U z` as a
germ. -/
theorem iteratedDeriv_eq_choose_factorial_mul_of_eventuallyEq_pow_mul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f U : 𝕜 → 𝕜} (n r : ℕ)
    (hfac : f =ᶠ[nhds 0] fun z => z ^ n * U z)
    (hU : ContDiffAt 𝕜 (n + r) U 0) :
    iteratedDeriv (n + r) f 0 =
      ((n + r).choose n : 𝕜) * (n.factorial : 𝕜) *
        iteratedDeriv r U 0 := by
  exact (hfac.iteratedDeriv_eq (n + r)).trans
    (iteratedDeriv_pow_mul_zero_add n r hU)

/-- **All centered jets from a vector-valued local factorization.**  This is
the arbitrary-center germ form of `iteratedDeriv_pow_smul_zero_eq_ite`.
No nonzero hypothesis on the center and no regularity hypothesis on `f` are
needed. -/
theorem iteratedDeriv_eq_ite_of_eventuallyEq_sub_pow_smul
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f U : 𝕜 → E} {z₀ : 𝕜} (n k : ℕ)
    (hfac : f =ᶠ[nhds z₀] fun z => (z - z₀) ^ n • U z)
    (hU : ContDiffAt 𝕜 k U z₀) :
    iteratedDeriv k f z₀ =
      if n ≤ k then
        ((k.choose n : 𝕜) * (n.factorial : 𝕜)) •
          iteratedDeriv (k - n) U z₀
      else 0 := by
  have hshiftContDiff :
      ContDiffAt 𝕜 k (fun w : 𝕜 => z₀ + w) 0 :=
    contDiffAt_const.add contDiffAt_id
  have hshift :
      Tendsto (fun w : 𝕜 => z₀ + w) (nhds 0) (nhds z₀) := by
    have hcontinuous := hshiftContDiff.continuousAt
    change Tendsto (fun w : 𝕜 => z₀ + w) (nhds 0) (nhds (z₀ + 0)) at hcontinuous
    simpa only [add_zero] using hcontinuous
  have hfac0 :
      (fun w : 𝕜 => f (z₀ + w)) =ᶠ[nhds 0]
        fun w : 𝕜 => w ^ n • U (z₀ + w) := by
    simpa only [Function.comp_def, add_sub_cancel_left] using
      hfac.comp_tendsto hshift
  have hU_atShiftZero :
      ContDiffAt 𝕜 k U ((fun w : 𝕜 => z₀ + w) 0) := by
    simpa only [add_zero] using hU
  have hUshift :
      ContDiffAt 𝕜 k (fun w : 𝕜 => U (z₀ + w)) 0 :=
    hU_atShiftZero.fun_comp 0 hshiftContDiff
  have hfDerivShift :
      iteratedDeriv k (fun w : 𝕜 => f (z₀ + w)) 0 =
        iteratedDeriv k f z₀ := by
    simpa only [add_zero] using
      congrFun (iteratedDeriv_comp_const_add k f z₀) (0 : 𝕜)
  have hUDerivShift :
      iteratedDeriv (k - n) (fun w : 𝕜 => U (z₀ + w)) 0 =
        iteratedDeriv (k - n) U z₀ := by
    simpa only [add_zero] using
      congrFun (iteratedDeriv_comp_const_add (k - n) U z₀) (0 : 𝕜)
  calc
    iteratedDeriv k f z₀ =
        iteratedDeriv k (fun w : 𝕜 => f (z₀ + w)) 0 :=
      hfDerivShift.symm
    _ = iteratedDeriv k (fun w : 𝕜 => w ^ n • U (z₀ + w)) 0 :=
      hfac0.iteratedDeriv_eq k
    _ = if n ≤ k then
          ((k.choose n : 𝕜) * (n.factorial : 𝕜)) •
            iteratedDeriv (k - n) (fun w : 𝕜 => U (z₀ + w)) 0
        else 0 :=
      iteratedDeriv_pow_smul_zero_eq_ite n k hUshift
    _ = _ := by rw [hUDerivShift]

/-- **Division-free higher jets from a vector-valued centered germ.** -/
theorem iteratedDeriv_eq_choose_factorial_smul_of_eventuallyEq_sub_pow_smul
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f U : 𝕜 → E} {z₀ : 𝕜} (n r : ℕ)
    (hfac : f =ᶠ[nhds z₀] fun z => (z - z₀) ^ n • U z)
    (hU : ContDiffAt 𝕜 (n + r) U z₀) :
    iteratedDeriv (n + r) f z₀ =
      (((n + r).choose n : 𝕜) * (n.factorial : 𝕜)) •
        iteratedDeriv r U z₀ := by
  simpa only [if_pos (Nat.le_add_right n r), Nat.add_sub_cancel_left] using
    iteratedDeriv_eq_ite_of_eventuallyEq_sub_pow_smul
      (z₀ := z₀) n (n + r) hfac hU

/-- **All higher jets from a local factorization at an arbitrary center.**
If `f z = (z - z₀) ^ n * U z` near `z₀`, then its `(n+r)`-th jet at
`z₀` is the division-free binomial-factorial multiple of the `r`-th jet
of `U`. -/
theorem iteratedDeriv_eq_choose_factorial_mul_of_eventuallyEq_sub_pow_mul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f U : 𝕜 → 𝕜} {z₀ : 𝕜} (n r : ℕ)
    (hfac : f =ᶠ[nhds z₀] fun z => (z - z₀) ^ n * U z)
    (hU : ContDiffAt 𝕜 (n + r) U z₀) :
    iteratedDeriv (n + r) f z₀ =
      ((n + r).choose n : 𝕜) * (n.factorial : 𝕜) *
        iteratedDeriv r U z₀ := by
  simpa only [smul_eq_mul] using
    iteratedDeriv_eq_choose_factorial_smul_of_eventuallyEq_sub_pow_smul
      (z₀ := z₀) n r hfac hU

/-- **Leading jet of a factored function.**  The `n`-th derivative at zero
of `z ^ n * U z` is `n! * U 0`.  No derivatives of `U` beyond order `n`,
and no analyticity hypothesis, are required. -/
theorem iteratedDeriv_pow_mul_zero
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (n : ℕ) {U : 𝕜 → 𝕜} (hU : ContDiffAt 𝕜 n U 0) :
    iteratedDeriv n (fun z => z ^ n * U z) 0 =
      (n.factorial : 𝕜) * U 0 := by
  simpa using iteratedDeriv_pow_mul_zero_add n 0 hU

/-- **Leading jet from a local factorization.**  If `f z = z ^ n * U z`
throughout a neighborhood of zero, then the `n`-th derivative of `f` is
`n! * U 0`.  The function `f` itself needs no separately supplied
regularity hypothesis. -/
theorem iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f U : 𝕜 → 𝕜} (n : ℕ)
    (hfac : f =ᶠ[nhds 0] fun z => z ^ n * U z)
    (hU : ContDiffAt 𝕜 n U 0) :
    iteratedDeriv n f 0 = (n.factorial : 𝕜) * U 0 := by
  simpa using
    iteratedDeriv_eq_choose_factorial_mul_of_eventuallyEq_pow_mul
      n 0 hfac hU

end Fabius
