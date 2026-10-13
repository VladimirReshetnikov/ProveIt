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

theorem roth_threshold_le_szemerediThresholdAt_three (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThresholdAt 3 delta k := by
  have hu : (2 : Real) ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by linarith)
  have hu1 : (1 : Real) ≤ delta⁻¹ := by linarith
  have hu0 : (0 : Real) ≤ delta⁻¹ := by linarith
  have hx : (6 : Real) ≤ (2 : Real) ^ (k + 3 : Nat) := by
    have h6 : (2 : Real) ^ (3 : Nat) ≤ (2 : Real) ^ (k + 3 : Nat) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h64 : (6 : Real) ≤ (2 : Real) ^ (3 : Nat) := by norm_num
    linarith
  have hE : (42 : Real) ≤ (2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat)) := by
    have h64 : (2 : Real) ^ (6 : Real) ≤ (2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    have h64' : (2 : Real) ^ (6 : Real) = 64 := by
      rw [show (6 : Real) = ((6 : Nat) : Real) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hpow42 : delta⁻¹ ^ (42 : Nat) ≤
      delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat))) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by exact_mod_cast hE)
  have h41 : (2 : Real) ^ (41 : Nat) ≤ delta⁻¹ ^ (41 : Nat) :=
    pow_le_pow_left₀ (by norm_num) hu 41
  have hinner : 1 + 2 * (1000000000000 * delta⁻¹) ≤
      delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat))) := by
    have h41' : (2000000000001 : Real) ≤ delta⁻¹ ^ (41 : Nat) := by
      have : (2000000000001 : Real) ≤ (2 : Real) ^ (41 : Nat) := by norm_num
      linarith
    have h42 : delta⁻¹ ^ (42 : Nat) = delta⁻¹ * delta⁻¹ ^ (41 : Nat) := by ring
    nlinarith [mul_le_mul_of_nonneg_left h41' hu0, hpow42, h42, hu1]
  unfold szemerediThresholdAt
  apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    2 * Real.exp (1000000000000 * delta⁻¹) ≤
        2 * (2 : Real) ^ (2 * (1000000000000 * delta⁻¹)) :=
      mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
    _ = (2 : Real) ^ (1 + 2 * (1000000000000 * delta⁻¹)) := by
      rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner

theorem quadraticIntervalClosedThreshold_le_at_three {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ szemerediThresholdAt 3 delta 4 := by
  apply (quadraticIntervalClosedThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 128))) =
      szemerediThresholdAt 3 delta 4 := by
    unfold szemerediThresholdAt
    rw [show (2 : Real) ^ (4 + 3 : Nat) = 128 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 21 ≤ 128))

theorem fejerFiveTermThreshold_le_at_three {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ szemerediThresholdAt 3 delta 5 := by
  apply (fejerFiveTermThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 256))) =
      szemerediThresholdAt 3 delta 5 := by
    unfold szemerediThresholdAt
    rw [show (2 : Real) ^ (5 + 3 : Nat) = 256 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 73 ≤ 256))

/-- **Theorem 18.2 with `L + 3` at every length `L ≤ 5`.** -/
theorem theorem_18_2_L3_le_five {k : Nat} (hk : k ≤ 5) : Theorem182AtSharp 3 k := by
  rcases (by omega : k ≤ 3 ∨ k = 4 ∨ k = 5) with h | rfl | rfl
  · intro delta N hδ hδ2 hN A hA hc
    obtain ⟨a, d, hd, hap⟩ := roth_explicit_threshold delta N hδ
      ((roth_threshold_le_szemerediThresholdAt_three k hδ hδ2).trans hN) A hA hc
    exact ⟨a, d, hd, fun i hi => hap i (by omega)⟩
  · intro delta N hδ hδhalf hN A hA hcard
    exact hasNatAP_Icc_of_fin_interval
      (fun B hB => quadratic_interval_szemeredi_closed delta hδ (by linarith) N
        ((quadraticIntervalClosedThreshold_le_at_three hδ hδhalf).trans hN) B hB) A hA hcard
  · intro delta N hδ hδhalf hN A hA hcard
    exact natural_five_term_fejer delta hδ (by linarith only [hδhalf]) N
      ((fejerFiveTermThreshold_le_at_three hδ hδhalf).trans hN) A hA hcard

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- **The inputs of the final route**: recurrence profiles with family constants
`Kc`, `pc` at most `2^(2^(4k+16))`, and a progression phase partition. -/
structure FinalInputs where
  Kc : Nat → Nat
  pc : Nat → Nat
  two_le_Kc : ∀ k, 2 ≤ Kc k
  pc_pos : ∀ k, 0 < pc k
  profile : ∀ k, 1 ≤ k →
    Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k))
  const : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))
  phase : ∃ (K : Real) (p : Nat), ProgressionPhasePartition K p ∧ 0 < p ∧ K ≤ 2 ^ p ∧
    (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)

namespace FinalInputs

variable (I : FinalInputs)
include I

/-- Theorem 18.1 at `d + c` for `d ≥ 4`, once the envelope fits `2^(c+2)·2^(d-2)`. -/
theorem theorem_18_1_of_fit {c d : Nat} (hd : 4 ≤ d)
    (hfit : polyGenMuJT3 (d - 2) + 1 ≤ 2 ^ (c + 2) * 2 ^ (d - 2)) : Theorem181AtSharp c d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
  have henv := polyEnvBound_allJT3 I.Kc I.pc I.two_le_Kc I.pc_pos I.profile I.const hpp hp hK hpB
    (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rwa [show d + c = (c + 2) + (d - 2) by omega, pow_add]

/-- Theorem 18.2 at `L + c` for `L ≥ 6`, once the envelope fits `2^(c+4)·2^(L-4)`. -/
theorem theorem_18_2_of_fit {c L : Nat} (hL : 6 ≤ L)
    (hfit : genMuXK3 (L - 4) + 2 * (L - 4) + 22 ≤ 2 ^ (c + 4) * 2 ^ (L - 4)) :
    Theorem182AtSharp c L := by
  have henv := envBound_allXK3 I.Kc I.pc I.two_le_Kc I.pc_pos I.profile I.const (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXK3_ge (k := L - 4) (by omega)
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXK3 (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXK3 (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv (by omega) hLμ ?_
  rw [show L + c = (c + 4) + (L - 4) by omega, pow_add]
  omega

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2`.** -/
theorem theorem_18_1_d2 {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d :=
  I.theorem_18_1_of_fit (by omega) (polyGenMuJT3_fit16 (by omega))

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 3`.** -/
theorem theorem_18_1_d3 {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 3 d :=
  I.theorem_18_1_of_fit (by omega) (polyGenMuJT3_fit32 (by omega))

/-- **Theorem 18.1 at every degree with `d + 4`.** -/
theorem theorem_18_1_d4 (d : Nat) : Theorem181AtSharp 4 d := by
  match d with
  | 0 => exact theorem_18_1_d4_degree_zero
  | 1 => exact theorem_18_1_d4_degree_one
  | 2 => exact theorem_18_1_d4_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
    exact theorem_18_1_d4_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact I.theorem_18_1_of_fit (by omega) (polyGenMuJT3_fit64 (by omega))

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 0`.** -/
theorem theorem_18_2_L0 {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 0 L :=
  I.theorem_18_2_of_fit (by omega) (genMuXK3_fit16 (by omega))

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 1`.** -/
theorem theorem_18_2_L1 {L : Nat} (hL : 11 ≤ L) : Theorem182AtSharp 1 L :=
  I.theorem_18_2_of_fit (by omega) (genMuXK3_fit32 (by omega))

/-- **Theorem 18.2 at every length `L ≥ 8` with `L + 2`.** -/
theorem theorem_18_2_L2 {L : Nat} (hL : 8 ≤ L) : Theorem182AtSharp 2 L :=
  I.theorem_18_2_of_fit (by omega) (genMuXK3_fit64 (by omega))

/-- **Theorem 18.2 at every length with `L + 3`.** -/
theorem theorem_18_2_L3 (L : Nat) : Theorem182AtSharp 3 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L3_le_five (by omega)
  · exact I.theorem_18_2_of_fit h (genMuXK3_fit128 (by omega))

end FinalInputs

end LeanProofs.GowersSzemeredi
