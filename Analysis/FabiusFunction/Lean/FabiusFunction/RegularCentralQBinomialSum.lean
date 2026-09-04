import FabiusFunction.CentralQBinomialReduction
import FabiusFunction.QGaussFullDomain
import FabiusFunction.QGammaMeromorphic

/-!
# A regular central q-binomial sum

For `0 < q < 1` and a complex parameter `alpha`, this file proves

`sum_k [2k,k]_(q^2) q^k / ((-q;q)_(2k) [2k+1+alpha]_q)
  = Gamma_(q^2)(3/2) Gamma_(q^2)((alpha+1)/2) / Gamma_(q^2)((alpha+2)/2)`.

The proof first applies the division form of the central Gaussian-binomial
reduction, identifies the resulting series with a scalar multiple of a
`2phi1`, and invokes the full-domain q-Gauss summation.  Two one-factor
shifts reduce its product value to the displayed q-gamma quotient.

The sole parameter hypothesis says that
`(q^(alpha+1);q^2)_infinity` is nonzero.  By the exact zero-set theorem for
the infinite q-Pochhammer symbol, this is precisely the simultaneous
nonvanishing condition for the generalized q-numbers in the summand.  In
particular it does not exclude the even negative integral parameters, where
the reciprocal q-gamma factor and the product evaluation both vanish.
-/

set_option autoImplicit false

namespace Fabius

open scoped BigOperators

/-- The complex generalized q-number `[z]_q = (1 - q^z) / (1 - q)` for a
real nome `q`. -/
noncomputable def qNumberC (q : ℝ) (z : ℂ) : ℂ :=
  (1 - (q : ℂ) ^ z) / (1 - (q : ℂ))

/-- The `k`-th summand in the regular central q-binomial evaluation. -/
noncomputable def regularCentralQBinomialTerm (q : ℝ) (alpha : ℂ) (k : ℕ) : ℂ :=
  gaussianBinomial ((q : ℂ) ^ 2) (2 * k) k * (q : ℂ) ^ k /
    (finiteQPochhammerIn (-(q : ℂ)) (q : ℂ) (2 * k) *
      qNumberC q (alpha + (2 * k + 1 : ℕ)))

private theorem ofReal_sq_cpow (q : ℝ) (hq0 : 0 < q) (z : ℂ) :
    (((q ^ 2 : ℝ) : ℂ) ^ z) = (q : ℂ) ^ (2 * z) := by
  rw [show ((q ^ 2 : ℝ) : ℂ) = (q : ℂ) * (q : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg hq0.le hq0.le,
    ← Complex.cpow_add _ _ (by exact_mod_cast hq0.ne')]
  congr 1
  ring

/-- **Regular central q-binomial sum** (`thm:regular-central-sum`).

For `0 < q < 1`, the regular central series has the stated q-gamma value.
The hypothesis on `(q^(alpha+1);q^2)_infinity` exactly packages the
nonvanishing of every generalized q-number occurring in the summand. -/
theorem hasSum_regularCentralQBinomial
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {alpha : ℂ}
    (halpha :
      qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) ≠ 0) :
    HasSum (regularCentralQBinomialTerm q alpha)
      (qGammaC (q ^ 2) (3 / 2 : ℂ) *
        qGammaC (q ^ 2) ((alpha + 1) / 2) /
        qGammaC (q ^ 2) ((alpha + 2) / 2)) := by
  have hq : ‖(q : ℂ)‖ < 1 := norm_ofReal_lt_one hq0 hq1
  have hq_ne : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hone_sub_q : (1 - (q : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hq1.ne')
  have hQ : ‖(q : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg (q : ℂ)) hq (by norm_num)
  have hA : (q : ℂ) ^ (alpha + 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hq_ne)
  have hAQ :
      (q : ℂ) ^ (alpha + 1) * (q : ℂ) ^ 2 =
        (q : ℂ) ^ (alpha + 3) := by
    rw [← Complex.cpow_natCast (q : ℂ) 2,
      ← Complex.cpow_add _ _ hq_ne]
    congr 1
    ring
  have hshift_alpha :
      qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) =
        (1 - (q : ℂ) ^ (alpha + 1)) *
          qPochhammerInfIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) := by
    simpa only [hAQ] using
      qPochhammerInfIn_succ_shift ((q : ℂ) ^ (alpha + 1)) hQ
  have hshift_alpha_ne :
      (1 - (q : ℂ) ^ (alpha + 1)) *
          qPochhammerInfIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) ≠ 0 := by
    rw [← hshift_alpha]
    exact halpha
  have hone_sub_A : (1 - (q : ℂ) ^ (alpha + 1)) ≠ 0 :=
    left_ne_zero_of_mul hshift_alpha_ne
  have hC :
      qPochhammerInfIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) ≠ 0 :=
    right_ne_zero_of_mul hshift_alpha_ne
  have hqInf :
      qPochhammerInfIn (q : ℂ) ((q : ℂ) ^ 2) ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hQ hq
  have hshift_q :
      qPochhammerInfIn (q : ℂ) ((q : ℂ) ^ 2) =
        (1 - (q : ℂ)) *
          qPochhammerInfIn ((q : ℂ) ^ 3) ((q : ℂ) ^ 2) := by
    convert qPochhammerInfIn_succ_shift (q : ℂ) hQ using 1 <;> ring
  have hq3Inf :
      qPochhammerInfIn ((q : ℂ) ^ 3) ((q : ℂ) ^ 2) ≠ 0 := by
    have h :
        (1 - (q : ℂ)) *
            qPochhammerInfIn ((q : ℂ) ^ 3) ((q : ℂ) ^ 2) ≠ 0 := by
      rw [← hshift_q]
      exact hqInf
    exact right_ne_zero_of_mul h

  have hca :
      (q : ℂ) ^ (alpha + 3) / (q : ℂ) =
        (q : ℂ) ^ (alpha + 2) := by
    apply (div_eq_iff hq_ne).2
    rw [← Complex.cpow_one (q : ℂ),
      ← Complex.cpow_add _ _ hq_ne]
    congr 1
    ring
  have hcb :
      (q : ℂ) ^ (alpha + 3) / (q : ℂ) ^ (alpha + 1) =
        (q : ℂ) ^ 2 := by
    apply (div_eq_iff hA).2
    simpa only [mul_comm] using hAQ.symm
  have hz :
      (q : ℂ) ^ (alpha + 3) /
          ((q : ℂ) * (q : ℂ) ^ (alpha + 1)) =
        (q : ℂ) := by
    apply (div_eq_iff (mul_ne_zero hq_ne hA)).2
    calc
      (q : ℂ) ^ (alpha + 3) =
          (q : ℂ) ^ (alpha + 1) * (q : ℂ) ^ 2 := hAQ.symm
      _ = (q : ℂ) * ((q : ℂ) * (q : ℂ) ^ (alpha + 1)) := by ring

  have hgauss := hasSum_q_gauss
    (q := (q : ℂ) ^ 2) (a := (q : ℂ))
    (b := (q : ℂ) ^ (alpha + 1))
    (c := (q : ℂ) ^ (alpha + 3))
    hQ hq_ne hA hC (by simpa only [hz] using hq)
  rw [hca, hcb, hz] at hgauss
  have hscaled := hgauss.mul_left (qNumberC q (alpha + 1))⁻¹

  have hproduct :
      (qNumberC q (alpha + 1))⁻¹ *
          (qPochhammerInfIn ((q : ℂ) ^ (alpha + 2)) ((q : ℂ) ^ 2) *
              qPochhammerInfIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) /
            (qPochhammerInfIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) *
              qPochhammerInfIn (q : ℂ) ((q : ℂ) ^ 2))) =
        qPochhammerInfIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) *
            qPochhammerInfIn ((q : ℂ) ^ (alpha + 2)) ((q : ℂ) ^ 2) /
          (qPochhammerInfIn ((q : ℂ) ^ 3) ((q : ℂ) ^ 2) *
            qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2)) := by
    unfold qNumberC
    rw [hshift_q, hshift_alpha]
    field_simp [hone_sub_q, hone_sub_A, hC, hq3Inf]
    ring
  rw [hproduct] at hscaled

  have hregular :
      HasSum (regularCentralQBinomialTerm q alpha)
        (qPochhammerInfIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) *
            qPochhammerInfIn ((q : ℂ) ^ (alpha + 2)) ((q : ℂ) ^ 2) /
          (qPochhammerInfIn ((q : ℂ) ^ 3) ((q : ℂ) ^ 2) *
            qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2))) := by
    refine hscaled.congr_fun fun k => ?_
    have hneg :
        finiteQPochhammerIn (-(q : ℂ)) (q : ℂ) (2 * k) ≠ 0 :=
      finiteQPochhammerIn_ne_zero_of_norm_lt_one hq (by simpa only [norm_neg] using hq) _
    have hQk :
        finiteQPochhammerIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) k ≠ 0 :=
      finiteQPochhammerIn_self_ne_zero hQ k
    have hCk :
        finiteQPochhammerIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) k ≠ 0 :=
      finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero
        ((q : ℂ) ^ (alpha + 3)) hQ hC k
    have hAkpow :
        (q : ℂ) ^ (alpha + 1) * ((q : ℂ) ^ 2) ^ k =
          (q : ℂ) ^ (alpha + (2 * k + 1 : ℕ)) := by
      rw [← pow_mul, ← Complex.cpow_natCast,
        ← Complex.cpow_add _ _ hq_ne]
      congr 1
      push_cast
      ring
    have htel :
        finiteQPochhammerIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) k *
            (1 - (q : ℂ) ^ (alpha + (2 * k + 1 : ℕ))) =
          (1 - (q : ℂ) ^ (alpha + 1)) *
            finiteQPochhammerIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) k := by
      calc
        finiteQPochhammerIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) k *
              (1 - (q : ℂ) ^ (alpha + (2 * k + 1 : ℕ))) =
            finiteQPochhammerIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) (k + 1) := by
              rw [finiteQPochhammerIn_succ, hAkpow]
        _ = (1 - (q : ℂ) ^ (alpha + 1)) *
              finiteQPochhammerIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) k := by
              rw [finiteQPochhammerIn_succ_shift, hAQ]
    have hone_sub_Ak :
        (1 - (q : ℂ) ^ (alpha + (2 * k + 1 : ℕ))) ≠ 0 := by
      have hleft :
          finiteQPochhammerIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) k *
              (1 - (q : ℂ) ^ (alpha + (2 * k + 1 : ℕ))) ≠ 0 := by
        rw [htel]
        exact mul_ne_zero hone_sub_A hCk
      exact right_ne_zero_of_mul hleft
    have hreciprocal :
        (qNumberC q (alpha + (2 * k + 1 : ℕ)))⁻¹ =
          (qNumberC q (alpha + 1))⁻¹ *
            finiteQPochhammerIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) k /
            finiteQPochhammerIn ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) k := by
      unfold qNumberC
      field_simp [hone_sub_q, hone_sub_A, hone_sub_Ak, hCk]
      linear_combination (1 - (q : ℂ)) * htel
    have hcentral := central_gaussianBinomial_sq_div (q : ℂ) k hneg hQk
    calc
      regularCentralQBinomialTerm q alpha k =
          (gaussianBinomial ((q : ℂ) ^ 2) (2 * k) k /
              finiteQPochhammerIn (-(q : ℂ)) (q : ℂ) (2 * k)) *
            (q : ℂ) ^ k *
            (qNumberC q (alpha + (2 * k + 1 : ℕ)))⁻¹ := by
              unfold regularCentralQBinomialTerm
              ring
      _ = (finiteQPochhammerIn (q : ℂ) ((q : ℂ) ^ 2) k /
              finiteQPochhammerIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) k) *
            (q : ℂ) ^ k *
            (qNumberC q (alpha + (2 * k + 1 : ℕ)))⁻¹ := by rw [hcentral]
      _ = (qNumberC q (alpha + 1))⁻¹ *
            twoPhiOneTerm (q : ℂ) ((q : ℂ) ^ (alpha + 1))
              ((q : ℂ) ^ (alpha + 3)) ((q : ℂ) ^ 2) (q : ℂ) k := by
              rw [hreciprocal]
              unfold twoPhiOneTerm
              ring

  have hbase : (((q ^ 2 : ℝ) : ℂ)) = (q : ℂ) ^ 2 := by
    push_cast
    ring
  have hpow_three_halves :
      (((q ^ 2 : ℝ) : ℂ) ^ (3 / 2 : ℂ)) = (q : ℂ) ^ 3 := by
    rw [ofReal_sq_cpow q hq0, ← Complex.cpow_natCast (q : ℂ) 3]
    congr 1
    ring
  have hpow_alpha_one :
      (((q ^ 2 : ℝ) : ℂ) ^ ((alpha + 1) / 2)) =
        (q : ℂ) ^ (alpha + 1) := by
    rw [ofReal_sq_cpow q hq0]
    congr 1
    ring
  have hpow_alpha_two :
      (((q ^ 2 : ℝ) : ℂ) ^ ((alpha + 2) / 2)) =
        (q : ℂ) ^ (alpha + 2) := by
    rw [ofReal_sq_cpow q hq0]
    congr 1
    ring
  have hq_sq_lt : q ^ 2 < 1 := by
    nlinarith [mul_pos hq0 (sub_pos.mpr hq1)]
  have hone_sub_Q : (1 - (((q ^ 2 : ℝ) : ℂ))) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hq_sq_lt.ne')
  have hone_sub_Q_complex : (1 - (q : ℂ) ^ 2) ≠ 0 := by
    simpa only [← hbase] using hone_sub_Q
  have hbasePow (z : ℂ) :
      (1 - (q : ℂ) ^ 2) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hone_sub_Q_complex)
  have hpow_cancel :
      (1 - (((q ^ 2 : ℝ) : ℂ))) ^ (1 - (3 / 2 : ℂ)) *
          (1 - (((q ^ 2 : ℝ) : ℂ))) ^ (1 - (alpha + 1) / 2) =
        (1 - (((q ^ 2 : ℝ) : ℂ))) ^ (1 - (alpha + 2) / 2) := by
    rw [← Complex.cpow_add _ _ hone_sub_Q]
    congr 1
    ring
  have hQInf :
      qPochhammerInfIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) ≠ 0 :=
    qPochhammerInfIn_self_ne_zero hQ
  have hgamma :
      qPochhammerInfIn ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) *
            qPochhammerInfIn ((q : ℂ) ^ (alpha + 2)) ((q : ℂ) ^ 2) /
          (qPochhammerInfIn ((q : ℂ) ^ 3) ((q : ℂ) ^ 2) *
            qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2)) =
        qGammaC (q ^ 2) (3 / 2 : ℂ) *
            qGammaC (q ^ 2) ((alpha + 1) / 2) /
          qGammaC (q ^ 2) ((alpha + 2) / 2) := by
    by_cases halpha_two :
        qPochhammerInfIn ((q : ℂ) ^ (alpha + 2)) ((q : ℂ) ^ 2) = 0
    · rw [halpha_two]
      simp only [mul_zero, zero_div]
      unfold qGammaC
      rw [hpow_three_halves, hpow_alpha_one, hpow_alpha_two, hbase, halpha_two]
      simp
    · unfold qGammaC
      rw [hpow_three_halves, hpow_alpha_one, hpow_alpha_two,
        ← hpow_cancel, hbase]
      field_simp [hQInf, hq3Inf, halpha, halpha_two, hbasePow]
      ring
  rw [← hgamma]
  exact hregular

end Fabius
