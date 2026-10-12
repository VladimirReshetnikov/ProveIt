import GowersSzemeredi.Proofs18CoverSharperLowDegrees

/-! **Theorem 18.1 with exponent `α^(2^(2^(d+6)))` at degrees `0, …, 3`**
(Notes L.16d).

`Proofs18CoverSharperLowDegrees` with `7` replaced by `6` (generated). The
corpus exponents at degrees `0, 1, 2` are fixed powers of `α` (at most
`α^49462`), far above `α^(2^(2^(d+6)))`, and degree three comes from the
polynomial base envelope `PolyEnvBound 3 74`, since `74 + 1 ≤ 2^(3+6)`.
With `Proofs18CoverFejerHeadline` this gives Theorem 18.1 at `d + 6` in every
degree. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem theorem_18_1_d6_degree_zero : Theorem181AtSharp 6 0 := by
  intro alpha hα _hα2
  refine ⟨1, fun N _ _ _ A hnot => ?_⟩
  exfalso
  apply hnot
  have hsum : ∀ a : Point N 0, ∑ s : ZMod N, cubeDifference (balanced A) a s = 0 := by
    intro a
    simp only [cubeDifference, List.ofFn_zero, iteratedDifference]
    exact sum_balanced A
  show ∑ a : Point N 0, ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 ≤
    alpha * (N : Real) ^ (0 + 2)
  have hα0 : 0 ≤ alpha * (N : Real) ^ (0 + 2) := by positivity
  first
    | (simp only [hsum, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero]; exact hα0)
    | (simp [hsum]; done)
    | (simp [hsum]; positivity)

theorem section18ExponentAt6_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 6 alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  have hα1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have h20 : (2 : Real) ^ (-(20 : Int)) = (1 / 2) ^ (20 : Nat) := by norm_num
  have hB : alpha ^ (20 : Nat) ≤ (2 : Real) ^ (-(20 : Int)) := by
    rw [h20]
    exact pow_le_pow_left₀ hα.le hα2 _
  have hexp : (24740 : Nat) ≤ 2 ^ 2 ^ (2 + 6) :=
    (by norm_num : (24740 : Nat) ≤ 2 ^ 15).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  unfold section18ExponentAt quadraticDiscrepancyParameter
  calc alpha ^ 2 ^ 2 ^ (2 + 6) ≤ alpha ^ (24740 : Nat) :=
        pow_le_pow_of_le_one hα.le hα1 hexp
    _ = alpha ^ (20 : Nat) * alpha ^ 2 * alpha ^ (24718 : Nat) := by ring
    _ ≤ (2 : Real) ^ (-(20 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity)) hA
          (by positivity) (by positivity)

theorem section18ExponentAt6_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 6 alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  have hα1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have h14 : (2 : Real) ^ (-(14 : Real)) = (1 / 2) ^ (14 : Nat) := by
    rw [Real.rpow_neg (by norm_num), show (14 : Real) = ((14 : Nat) : Real) by norm_num,
      Real.rpow_natCast]
    norm_num
  have hexp : (49462 : Nat) ≤ 2 ^ 2 ^ (2 + 6) :=
    (by norm_num : (49462 : Nat) ≤ 2 ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hC : alpha ^ (14 : Nat) ≤ (1 / 2) ^ (14 : Nat) := pow_le_pow_left₀ hα.le hα2 _
  have hD : (alpha ^ (24718 : Nat)) ^ 2 ≤ ((alpha / 2) ^ (12359 : Nat)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  have hE : alpha ^ (12 : Nat) ≤ (1 / 2) ^ (12 : Nat) := pow_le_pow_left₀ hα.le hα2 _
  unfold section18ExponentAt quadraticDiscrepancyExponent cor711Exponent
  rw [h14]
  calc alpha ^ 2 ^ 2 ^ (2 + 6) ≤ alpha ^ (49462 : Nat) :=
        pow_le_pow_of_le_one hα.le hα1 hexp
    _ = alpha ^ (14 : Nat) * (alpha ^ (24718 : Nat)) ^ 2 * alpha ^ (12 : Nat) := by ring
    _ ≤ (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * (1 / 2) ^ (12 : Nat) :=
        mul_le_mul (mul_le_mul hC hD (by positivity) (by positivity)) hE
          (by positivity) (by positivity)
    _ = (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * ((1 : Nat) : Real)⁻¹ /
          4096 := by
        first | (norm_num; done) | (norm_num; ring) | ring

theorem theorem_18_1_d6_degree_two : Theorem181AtSharp 6 2 := by
  apply Theorem181AtSharp.of_function_discrepancy
  intro alpha hα hα2
  exact ⟨quadraticDiscrepancyParameter alpha, quadraticDiscrepancyExponent alpha,
    quadraticExponentialThreshold alpha,
    section18ExponentAt6_two_le_quadraticDiscrepancyParameter hα hα2,
    section18ExponentAt6_two_le_quadraticDiscrepancyExponent hα hα2,
    quadratic_function_discrepancy_bound hα (by linarith)⟩

theorem theorem_18_1_d6_degree_one : Theorem181AtSharp 6 1 := by
  intro alpha hα hα2
  have hα1 : alpha ≤ 1 := by linarith
  let e : Real := 1 / 2
  let beta : Real := Real.sqrt alpha
  have hβ : 0 < beta := Real.sqrt_pos.mpr hα
  have he : (0 : Real) < e := by norm_num [e]
  refine ⟨⌈positivePowerThreshold (phaseInverseConstant 1 beta 1) 1
      (phaseInverseExponent 1 e)⌉₊, fun N _ _ hN A hnot => ?_⟩
  have hNth : positivePowerThreshold (phaseInverseConstant 1 beta 1) 1
      (phaseInverseExponent 1 e) ≤ (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN1 : (1 : Real) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨r, hr⟩ := linear_nonuniformity_large_fourier (balanced A) alpha hα.le
    (balanced_discValued A) hnot
  have hpoly : ∀ _i : Fin 1, PolynomialOn 1 Finset.univ (fun x : ZMod N => r * x) := by
    intro _
    refine ⟨![0, r], fun x _ => ?_⟩
    simp [Fin.sum_univ_two]
  have hcount : ((1 : Nat) : Real) ≤ 1 * (N : Real) ^ (1 - e) := by
    rw [Nat.cast_one, one_mul]
    exact Real.one_le_rpow hN1 (by norm_num [e])
  have hdis : beta * N ≤ ∑ _i : Fin 1,
      ‖∑ x ∈ (wholeModAP N).carrier, phaseTwist (balanced A) (fun x => r * x) x‖ := by
    rw [Fin.sum_univ_one, wholeModAP_carrier, ← fourier_eq_sum_phaseTwist]
    exact hr.le
  obtain ⟨J, R, hR, hRproper, hsize, hdisR⟩ :=
    polynomial_phase_inverse_partition (k := 1) (K := 1) le_rfl he hβ one_pos (balanced A)
      (balanced_discValued A) (fun _ => wholeModAP N) (fun _ => fun x => r * x) hpoly
      wholeModAP_partition hcount hdis hNth
  have hexp1 : section18ExponentAt 6 alpha 1 ≤ phaseInverseExponent 1 e := by
    have hpc : phaseInverseExponent 1 e = (1 / 2) ^ (6 : Nat) := by
      norm_num [phaseInverseExponent, polynomialPartitionConstant, e, Nat.factorial]
    have h6 : (6 : Nat) ≤ 2 ^ 2 ^ (1 + 6) :=
      (by norm_num : (6 : Nat) ≤ 2 ^ 3).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    rw [hpc]
    unfold section18ExponentAt
    exact (pow_le_pow_of_le_one hα.le hα1 h6).trans (pow_le_pow_left₀ hα.le hα2 6)
  have hexp2 : section18ExponentAt 6 alpha 1 ≤ beta / 2 := by
    have hsq : alpha ≤ Real.sqrt alpha := by
      calc alpha = Real.sqrt (alpha ^ 2) := (Real.sqrt_sq hα.le).symm
        _ ≤ Real.sqrt alpha := Real.sqrt_le_sqrt (by nlinarith)
    have h2 : (2 : Nat) ≤ 2 ^ 2 ^ (1 + 6) :=
      (by norm_num : (2 : Nat) ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    unfold section18ExponentAt
    calc alpha ^ 2 ^ 2 ^ (1 + 6) ≤ alpha ^ 2 := pow_le_pow_of_le_one hα.le hα1 h2
      _ ≤ alpha / 2 := by
        rw [pow_two]
        linarith only [mul_le_mul_of_nonneg_left hα2 hα.le]
      _ ≤ beta / 2 := by
        have : alpha ≤ beta := hsq
        linarith
  refine ⟨J, R, hR, hRproper, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN1 hexp1).trans hsize
  · exact (mul_le_mul_of_nonneg_right hexp2 (Nat.cast_nonneg N)).trans hdisR

/-- **Theorem 18.1 at degree three with exponent `α^(2^(2^9))`**, from a phase
partition. -/
theorem theorem_18_1_d6_three_of_phase_partition
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    Theorem181AtSharp 6 3 :=
  theorem181AtSharp_of_polyEnvBound (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
    (by norm_num)

end LeanProofs.GowersSzemeredi
