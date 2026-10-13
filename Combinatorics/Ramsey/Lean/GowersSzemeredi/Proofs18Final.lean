import GowersSzemeredi.Proofs18FinalEnvelopes
import GowersSzemeredi.Proofs18CoverHeadlineFrom

/-! **The final route** (Notes L.16-final).

All the final bounds from one structure of inputs, `FinalInputs`: recurrence
profiles with polynomial family constants, and a progression phase partition
(the corpus supplies both; see `Proofs18CoverFejerAllDegrees`). Over the class
table `tDegT3`:
* Theorem 18.1 with `d + 4` in every degree, `d + 3` for `d ≥ 8`, and
  `d + 2` for `d ≥ 11` (degrees `0, …, 3` from the corpus exponents and the
  polynomial base envelope);
* Theorem 18.2 with `L + 3` in every length, `L + 2` for `L ≥ 8`, `L + 1` for
  `L ≥ 11`, and `L + 0` for `L ≥ 13` (lengths `L ≤ 5` from the corpus's
  explicit thresholds). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

theorem theorem_18_1_d4_degree_zero : Theorem181AtSharp 4 0 := by
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

theorem section18ExponentAt4_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 4 alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  have hα1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have h20 : (2 : Real) ^ (-(20 : Int)) = (1 / 2) ^ (20 : Nat) := by norm_num
  have hB : alpha ^ (20 : Nat) ≤ (2 : Real) ^ (-(20 : Int)) := by
    rw [h20]
    exact pow_le_pow_left₀ hα.le hα2 _
  have hexp : (24740 : Nat) ≤ 2 ^ 2 ^ (2 + 4) :=
    (by norm_num : (24740 : Nat) ≤ 2 ^ 15).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  unfold section18ExponentAt quadraticDiscrepancyParameter
  calc alpha ^ 2 ^ 2 ^ (2 + 4) ≤ alpha ^ (24740 : Nat) :=
        pow_le_pow_of_le_one hα.le hα1 hexp
    _ = alpha ^ (20 : Nat) * alpha ^ 2 * alpha ^ (24718 : Nat) := by ring
    _ ≤ (2 : Real) ^ (-(20 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity)) hA
          (by positivity) (by positivity)

theorem section18ExponentAt4_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 4 alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  have hα1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have h14 : (2 : Real) ^ (-(14 : Real)) = (1 / 2) ^ (14 : Nat) := by
    rw [Real.rpow_neg (by norm_num), show (14 : Real) = ((14 : Nat) : Real) by norm_num,
      Real.rpow_natCast]
    norm_num
  have hexp : (49462 : Nat) ≤ 2 ^ 2 ^ (2 + 4) :=
    (by norm_num : (49462 : Nat) ≤ 2 ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hC : alpha ^ (14 : Nat) ≤ (1 / 2) ^ (14 : Nat) := pow_le_pow_left₀ hα.le hα2 _
  have hD : (alpha ^ (24718 : Nat)) ^ 2 ≤ ((alpha / 2) ^ (12359 : Nat)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  have hE : alpha ^ (12 : Nat) ≤ (1 / 2) ^ (12 : Nat) := pow_le_pow_left₀ hα.le hα2 _
  unfold section18ExponentAt quadraticDiscrepancyExponent cor711Exponent
  rw [h14]
  calc alpha ^ 2 ^ 2 ^ (2 + 4) ≤ alpha ^ (49462 : Nat) :=
        pow_le_pow_of_le_one hα.le hα1 hexp
    _ = alpha ^ (14 : Nat) * (alpha ^ (24718 : Nat)) ^ 2 * alpha ^ (12 : Nat) := by ring
    _ ≤ (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * (1 / 2) ^ (12 : Nat) :=
        mul_le_mul (mul_le_mul hC hD (by positivity) (by positivity)) hE
          (by positivity) (by positivity)
    _ = (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * ((1 : Nat) : Real)⁻¹ /
          4096 := by
        first | (norm_num; done) | (norm_num; ring) | ring

theorem theorem_18_1_d4_degree_two : Theorem181AtSharp 4 2 := by
  apply Theorem181AtSharp.of_function_discrepancy
  intro alpha hα hα2
  exact ⟨quadraticDiscrepancyParameter alpha, quadraticDiscrepancyExponent alpha,
    quadraticExponentialThreshold alpha,
    section18ExponentAt4_two_le_quadraticDiscrepancyParameter hα hα2,
    section18ExponentAt4_two_le_quadraticDiscrepancyExponent hα hα2,
    quadratic_function_discrepancy_bound hα (by linarith)⟩

theorem theorem_18_1_d4_degree_one : Theorem181AtSharp 4 1 := by
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
  have hexp1 : section18ExponentAt 4 alpha 1 ≤ phaseInverseExponent 1 e := by
    have hpc : phaseInverseExponent 1 e = (1 / 2) ^ (6 : Nat) := by
      norm_num [phaseInverseExponent, polynomialPartitionConstant, e, Nat.factorial]
    have h6 : (6 : Nat) ≤ 2 ^ 2 ^ (1 + 4) :=
      (by norm_num : (6 : Nat) ≤ 2 ^ 3).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    rw [hpc]
    unfold section18ExponentAt
    exact (pow_le_pow_of_le_one hα.le hα1 h6).trans (pow_le_pow_left₀ hα.le hα2 6)
  have hexp2 : section18ExponentAt 4 alpha 1 ≤ beta / 2 := by
    have hsq : alpha ≤ Real.sqrt alpha := by
      calc alpha = Real.sqrt (alpha ^ 2) := (Real.sqrt_sq hα.le).symm
        _ ≤ Real.sqrt alpha := Real.sqrt_le_sqrt (by nlinarith)
    have h2 : (2 : Nat) ≤ 2 ^ 2 ^ (1 + 4) :=
      (by norm_num : (2 : Nat) ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    unfold section18ExponentAt
    calc alpha ^ 2 ^ 2 ^ (1 + 4) ≤ alpha ^ 2 := pow_le_pow_of_le_one hα.le hα1 h2
      _ ≤ alpha / 2 := by
        rw [pow_two]
        linarith only [mul_le_mul_of_nonneg_left hα2 hα.le]
      _ ≤ beta / 2 := by
        have : alpha ≤ beta := hsq
        linarith
  refine ⟨J, R, hR, hRproper, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN1 hexp1).trans hsize
  · exact (mul_le_mul_of_nonneg_right hexp2 (Nat.cast_nonneg N)).trans hdisR

/-- **Theorem 18.1 at degree three with exponent `α^(2^(2^7))`**, from a phase
partition. -/
theorem theorem_18_1_d4_three_of_phase_partition
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    Theorem181AtSharp 4 3 :=
  theorem181AtSharp_of_polyEnvBound (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
    (by norm_num)

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

namespace FinalInputs

variable (I : FinalInputs)
include I

/-- **Theorem 18.1 at `d + c` from `d = k0 + 2`**, once the envelope fits `2^(c+2)·2^k` in
the dimensions `k0, …, 14` (beyond, the closed form gives `16·2^k`). -/
theorem theorem_18_1_of_fit {c d : Nat} (k0 : Nat) (hd : k0 + 2 ≤ d) (hk0 : 2 ≤ k0) (hc : 2 ≤ c)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → polyGenMuJT3 j + 1 ≤ 2 ^ (c + 2) * 2 ^ j) :
    Theorem181AtSharp c d := by
  have henv := I.polyEnvBound (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rw [show d + c = (c + 2) + (d - 2) by omega, pow_add]
  have hC : 16 ≤ 2 ^ (c + 2) :=
    le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact polyGenMuJT3_fit hC hsmall (by omega)

/-- **Theorem 18.2 at `L + c` from `L = k0 + 4`**, once the envelope fits `2^(c+4)·2^k` in
the dimensions `k0, …, 14`. -/
theorem theorem_18_2_of_fit {c L : Nat} (k0 : Nat) (hL : k0 + 4 ≤ L) (hk0 : 2 ≤ k0)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → genMuXK3 j + 2 * j + 22 ≤ 2 ^ (c + 4) * 2 ^ j) :
    Theorem182AtSharp c L := by
  have henv := I.envBound (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXK3_ge (k := L - 4) (by omega)
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXK3 (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXK3 (L - 4))
    omega
  have hC : 16 ≤ 2 ^ (c + 4) :=
    le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfit := genMuXK3_fit hC hsmall (by omega : k0 ≤ L - 4)
  refine theorem182AtSharp_of_envBound (by omega) henv (by omega) hLμ ?_
  rw [show L + c = (c + 4) + (L - 4) by omega, pow_add]
  omega

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2`.** -/
theorem theorem_18_1_d2 {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d :=
  I.theorem_18_1_of_fit 9 hd (by norm_num) le_rfl fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 3`.** -/
theorem theorem_18_1_d3 {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 3 d :=
  I.theorem_18_1_of_fit 6 hd (by norm_num) (by norm_num) fun j _ _ => by
    interval_cases j <;> decide +kernel

/-- **Theorem 18.1 at every degree with `d + 4`.** -/
theorem theorem_18_1_d4 (d : Nat) : Theorem181AtSharp 4 d := by
  match d with
  | 0 => exact theorem_18_1_d4_degree_zero
  | 1 => exact theorem_18_1_d4_degree_one
  | 2 => exact theorem_18_1_d4_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
    exact theorem_18_1_d4_three_of_phase_partition hpp hp hK hpB
  | d + 4 =>
    exact I.theorem_18_1_of_fit 2 (by omega) (by norm_num) (by norm_num) fun j _ _ => by
      interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 0`.** -/
theorem theorem_18_2_L0 {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 0 L :=
  I.theorem_18_2_of_fit 9 hL (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 1`.** -/
theorem theorem_18_2_L1 {L : Nat} (hL : 11 ≤ L) : Theorem182AtSharp 1 L :=
  I.theorem_18_2_of_fit 7 hL (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length `L ≥ 8` with `L + 2`.** -/
theorem theorem_18_2_L2 {L : Nat} (hL : 8 ≤ L) : Theorem182AtSharp 2 L :=
  I.theorem_18_2_of_fit 4 hL (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length with `L + 3`.** -/
theorem theorem_18_2_L3 (L : Nat) : Theorem182AtSharp 3 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L3_le_five (by omega)
  · exact I.theorem_18_2_of_fit 2 h (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

end FinalInputs

end LeanProofs.GowersSzemeredi
