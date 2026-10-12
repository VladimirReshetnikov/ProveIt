import GowersSzemeredi.Proofs18IntegerInverse

/-! The lower-degree bases for the genuine integer-progression inverse
theorem. The linear function bound works over every nonzero modulus. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def linearFunctionDiscrepancyThreshold (alpha : Real) : Real :=
  positivePowerThreshold (phaseInverseConstant 1 (Real.sqrt alpha) 1) 1
    (phaseInverseExponent 1 (1 / 2))

/-- The linear inverse bound applies to arbitrary disc-valued functions
and arbitrary nonzero cyclic moduli, including composite moduli. -/
theorem linear_function_discrepancy_partition {alpha : Real} (ha : 0 < alpha)
    (N : Nat) [NeZero N] (hN : linearFunctionDiscrepancyThreshold alpha ≤ N)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 1) :
    ∃ M : Nat, ∃ P : Fin M → ModAP N,
      IsPartition (fun i => (P i).carrier) Finset.univ ∧
      (∀ i, (P i).IsProper) ∧
      (N : Real) ^ (1 / 64 : Real) ≤ averageCellSize (fun i => (P i).carrier) ∧
      (Real.sqrt alpha / 2) * N ≤ ∑ i, ‖∑ s ∈ (P i).carrier, f s‖ := by
  classical
  have hβ : 0 < Real.sqrt alpha := Real.sqrt_pos.mpr ha
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨r, hr⟩ := linear_nonuniformity_large_fourier f alpha ha.le hf hnot
  have hpoly : ∀ _i : Fin 1, PolynomialOn 1 Finset.univ (fun x : ZMod N => r * x) := by
    intro i
    refine ⟨![0, r], fun x _ => ?_⟩
    simp [Fin.sum_univ_two]
  have hcount : ((1 : Nat) : Real) ≤ 1 * (N : Real) ^ (1 - (1 / 2 : Real)) := by
    simp only [Nat.cast_one, one_mul]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hdisc : Real.sqrt alpha * N ≤ ∑ _i : Fin 1,
      ‖∑ x ∈ (wholeModAP N).carrier, phaseTwist f (fun x => r * x) x‖ := by
    rw [Fin.sum_univ_one, wholeModAP_carrier, ← fourier_eq_sum_phaseTwist]
    exact hr.le
  obtain ⟨M, P, hP, hPr, hsize, hdis⟩ :=
    polynomial_phase_inverse_partition (k := 1) (K := 1) le_rfl
      (by norm_num : (0 : Real) < 1 / 2) hβ one_pos f hf
      (fun _ => wholeModAP N) (fun _ => fun x => r * x) hpoly
      wholeModAP_partition hcount hdisc hN
  refine ⟨M, P, hP, hPr, ?_, hdis⟩
  have hexp : phaseInverseExponent 1 (1 / 2) = (1 / 64 : Real) := by
    norm_num [phaseInverseExponent, polynomialPartitionConstant, Nat.factorial]
  simpa only [hexp] using hsize

theorem theorem_18_1_integer_zero (c : Nat) : Theorem181IntegerAt c 0 := by
  intro alpha ha ha2
  refine ⟨1, fun N _ _ _ A hnot => ?_⟩
  exfalso
  apply hnot
  have hsum : ∀ a : Point N 0, ∑ s : ZMod N, cubeDifference (balanced A) a s = 0 := by
    intro a
    simp only [cubeDifference, List.ofFn_zero, iteratedDifference]
    exact sum_balanced A
  show ∑ a : Point N 0, ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 ≤
    alpha * (N : Real) ^ (0 + 2)
  simp only [hsum, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero]
  positivity

/-- The linear base admits the much stronger `1+1` offset, with genuine
integer progressions. -/
theorem theorem_18_1_integer_one : Theorem181IntegerAt 1 1 := by
  apply Theorem181IntegerAt.of_function_discrepancy
  intro alpha ha ha2
  have ha1 : alpha ≤ 1 := by linarith
  have htwo : 2 ≤ (2 : Nat) ^ ((2 : Nat) ^ (1 + 1)) := by decide
  have height : 8 ≤ (2 : Nat) ^ ((2 : Nat) ^ (1 + 1)) := by decide
  have hsmall : section18ExponentAt 1 alpha 1 ≤ (1 / 256 : Real) := by
    calc
      section18ExponentAt 1 alpha 1 ≤ alpha ^ (8 : Nat) :=
        pow_le_pow_of_le_one ha.le ha1 height
      _ ≤ (1 / 2 : Real) ^ (8 : Nat) := pow_le_pow_left₀ ha.le ha2 _
      _ = 1 / 256 := by norm_num
  have hb : section18ExponentAt 1 alpha 1 ≤ Real.sqrt alpha / 2 := by
    have hroot : alpha ≤ Real.sqrt alpha := by
      calc
        alpha = Real.sqrt (alpha ^ 2) := (Real.sqrt_sq ha.le).symm
        _ ≤ Real.sqrt alpha := Real.sqrt_le_sqrt (by nlinarith)
    calc
      section18ExponentAt 1 alpha 1 ≤ alpha ^ 2 := pow_le_pow_of_le_one ha.le ha1 htwo
      _ ≤ alpha / 2 := by nlinarith
      _ ≤ Real.sqrt alpha / 2 := div_le_div_of_nonneg_right hroot (by norm_num)
  refine ⟨Real.sqrt alpha / 2, 1 / 64, linearFunctionDiscrepancyThreshold alpha,
    hb, by linarith, ?_⟩
  intro N _ _ hN f hf hnot
  exact linear_function_discrepancy_partition ha N hN f hf hnot

/-- A fixed power dominates both parameters of the quadratic inverse
throughout the source's density range. This does not fix a tower offset. -/
theorem quadratic_discrepancy_fixed_power_lower {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    alpha ^ (49462 : Nat) ≤ quadraticDiscrepancyParameter alpha ∧
      alpha ^ (49462 : Nat) ≤ quadraticDiscrepancyExponent alpha := by
  have ha1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc
      alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have hB : alpha ^ (20 : Nat) ≤ (2 : Real) ^ (-(20 : Int)) := by
    have h20 : (2 : Real) ^ (-(20 : Int)) = (1 / 2) ^ (20 : Nat) := by norm_num
    rw [h20]
    exact pow_le_pow_left₀ ha.le ha2 _
  constructor
  · have hp : alpha ^ (24740 : Nat) ≤ quadraticDiscrepancyParameter alpha := by
      unfold quadraticDiscrepancyParameter
      calc
        alpha ^ (24740 : Nat) = alpha ^ (20 : Nat) * alpha ^ 2 * alpha ^ (24718 : Nat) := by ring
        _ ≤ (2 : Real) ^ (-(20 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity)) hA
            (by positivity) (by positivity)
    exact (pow_le_pow_of_le_one ha.le ha1 (by omega : 24740 ≤ 49462)).trans hp
  · have h14 : (2 : Real) ^ (-(14 : Real)) = (1 / 2) ^ (14 : Nat) := by
      rw [Real.rpow_neg (by norm_num), show (14 : Real) = ((14 : Nat) : Real) by norm_num,
        Real.rpow_natCast]
      norm_num
    have hC : alpha ^ (14 : Nat) ≤ (1 / 2) ^ (14 : Nat) := pow_le_pow_left₀ ha.le ha2 _
    have hD : (alpha ^ (24718 : Nat)) ^ 2 ≤ ((alpha / 2) ^ (12359 : Nat)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hA 2
    have hE : alpha ^ (12 : Nat) ≤ (1 / 2) ^ (12 : Nat) := pow_le_pow_left₀ ha.le ha2 _
    unfold quadraticDiscrepancyExponent cor711Exponent
    rw [h14]
    calc
      alpha ^ (49462 : Nat) = alpha ^ (14 : Nat) * (alpha ^ (24718 : Nat)) ^ 2 * alpha ^ (12 : Nat) := by ring
      _ ≤ (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * (1 / 2) ^ (12 : Nat) :=
        mul_le_mul (mul_le_mul hC hD (by positivity) (by positivity)) hE
          (by positivity) (by positivity)
      _ = _ := by norm_num <;> ring

/-- The quadratic base admits genuine integer progressions at the much
stronger `2+2` offset. -/
theorem theorem_18_1_integer_two : Theorem181IntegerAt 2 2 := by
  apply Theorem181IntegerAt.of_function_discrepancy
  intro alpha ha ha2
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨hb, hs⟩ := quadratic_discrepancy_fixed_power_lower ha ha2
  have hexp : 49462 + 2 ≤ (2 : Nat) ^ ((2 : Nat) ^ (2 + 2)) := by decide
  have heps : section18ExponentAt 2 alpha 2 ≤ alpha ^ (49462 : Nat) / 4 := by
    have hαsq : alpha ^ 2 ≤ (1 / 4 : Real) := by nlinarith
    calc
      section18ExponentAt 2 alpha 2 ≤ alpha ^ (49462 + 2 : Nat) :=
        pow_le_pow_of_le_one ha.le ha1 hexp
      _ = alpha ^ (49462 : Nat) * alpha ^ 2 := pow_add _ _ _
      _ ≤ alpha ^ (49462 : Nat) * (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_left hαsq (by positivity)
      _ = alpha ^ (49462 : Nat) / 4 := by ring
  have hs0 : 0 < quadraticDiscrepancyExponent alpha := (pow_pos ha _).trans_le hs
  have hb0 : 0 ≤ alpha ^ (49462 : Nat) := by positivity
  refine ⟨quadraticDiscrepancyParameter alpha, quadraticDiscrepancyExponent alpha,
    quadraticExponentialThreshold alpha, by linarith, by linarith,
    quadratic_function_discrepancy_bound ha ha1⟩

/-- Every degree has the printed exponent and genuine integer
representatives. Degrees one, two, three and at least four have the
stronger offsets 1, 2, 4 and 7 respectively. -/
theorem theorem_18_1_integer_d7 (d : Nat) : Theorem181IntegerAt 7 d := by
  by_cases hd : d < 4
  · interval_cases d
    · exact theorem_18_1_integer_zero 7
    · exact theorem_18_1_integer_one.mono (by omega)
    · exact theorem_18_1_integer_two.mono (by omega)
    · exact theorem_18_1_integer_three.mono (by omega)
  · exact theorem_18_1_integer_d7_four_le (by omega)

theorem theorem_18_1_integer_at_printed (d : Nat) : Theorem181IntegerAt 10 d :=
  (theorem_18_1_integer_d7 d).mono (by omega)

/-- The source's Theorem 18.1 with the genuine integer-representative
interpretation of its progression partition. -/
def theorem_18_1_integer_representatives : Prop := ∀ d : Nat, Theorem181IntegerAt 10 d

theorem theorem_18_1_integer_representatives_holds : theorem_18_1_integer_representatives :=
  theorem_18_1_integer_at_printed

end LeanProofs.GowersSzemeredi
