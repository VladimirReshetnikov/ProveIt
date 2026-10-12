import GowersSzemeredi.Proofs05IntegerPartitionBounds
import GowersSzemeredi.Proofs18CoverSharperExplicit

/-! Genuine integer-progression versions of Theorem 18.1. Integer
refinement preserves discrepancy and costs a square root in average size.
The unused slack in the polynomial inverse envelopes absorbs that loss. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Theorem 18.1 at one degree and offset, with ordinary integer
representatives instead of only injective modular parameterizations. -/
def Theorem181IntegerAt (c k : Nat) : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha k →
        ∃ M : Nat, ∃ P : Fin M → ModAP N,
          IsPartition (fun i => (P i).carrier) Finset.univ ∧
          (∀ i, (P i).HasIntegerRepresentatives) ∧
          (N : Real) ^ section18ExponentAt c alpha k ≤
            averageCellSize (fun i => (P i).carrier) ∧
          section18ExponentAt c alpha k * N ≤
            ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s‖

theorem Theorem181IntegerAt.to_sharp {c k : Nat} (h : Theorem181IntegerAt c k) :
    Theorem181AtSharp c k := by
  intro alpha ha ha2
  obtain ⟨N0, hN0⟩ := h alpha ha ha2
  refine ⟨N0, fun N _ _ hN A hnot => ?_⟩
  obtain ⟨M, P, hP, hPr, hsize, hdisc⟩ := hN0 N hN A hnot
  exact ⟨M, P, hP, fun i => (hPr i).isProper, hsize, hdisc⟩

theorem Theorem181IntegerAt.mono {c c' k : Nat} (h : Theorem181IntegerAt c k)
    (hc : c ≤ c') : Theorem181IntegerAt c' k := by
  intro alpha ha ha2
  obtain ⟨N0, hN0⟩ := h alpha ha ha2
  refine ⟨N0, fun N _ _ hN A hnot => ?_⟩
  obtain ⟨M, P, hP, hPr, hsize, hdisc⟩ := hN0 N hN A hnot
  have he : section18ExponentAt c' alpha k ≤ section18ExponentAt c alpha k :=
    pow_le_pow_of_le_one ha.le (by linarith)
      (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  exact ⟨M, P, hP, hPr, (Real.rpow_le_rpow_of_exponent_le hN1 he).trans hsize,
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hdisc⟩

/-- A strictly larger size exponent pays for genuine refinement, while
the discrepancy coefficient is preserved. The modulus threshold remains
explicitly existential, as in the paper's Theorem 18.1. -/
theorem Theorem181IntegerAt.of_function_discrepancy {c k : Nat}
    (h : ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ beta sigma T : Real,
        section18ExponentAt c alpha k ≤ beta ∧
        section18ExponentAt c alpha k < sigma / 2 ∧
        FunctionDiscrepancyBound k alpha beta sigma T) : Theorem181IntegerAt c k := by
  intro alpha ha ha2
  obtain ⟨beta, sigma, T, hb, hs, hB⟩ := h alpha ha ha2
  obtain ⟨N1, hN1, hpower⟩ :=
    exists_integer_refinement_power_threshold (section18ExponentAt c alpha k) sigma hs
  refine ⟨max ⌈T⌉₊ N1, fun N _ _ hN A hnot => ?_⟩
  have hT : T ≤ (N : Real) :=
    (Nat.le_ceil T).trans (by exact_mod_cast le_trans (le_max_left _ _) hN)
  have hNpower : N1 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨M, P, hP, _, hsize, hdisc⟩ :=
    hB N hT (balanced A) (balanced_discValued A) hnot
  obtain ⟨L, R, href, hR, hRinteger, haverage⟩ :=
    integer_representative_refinement_average P hP
  refine ⟨L, R, hR, hRinteger, ?_, ?_⟩
  · calc
      (N : Real) ^ section18ExponentAt c alpha k ≤ Real.sqrt ((N : Real) ^ sigma) / 4 :=
        hpower N hNpower
      _ ≤ Real.sqrt (averageCellSize (fun i => (P i).carrier)) / 4 :=
        div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hsize) (by norm_num)
      _ ≤ averageCellSize (fun j => (R j).carrier) := haverage
  · calc
      section18ExponentAt c alpha k * N ≤ beta * N :=
        mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)
      _ ≤ ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s‖ := hdisc
      _ ≤ ∑ j, ‖∑ s ∈ (R j).carrier, balanced A s‖ :=
        IsRefinement.sum_norm_mono (fun i => (P i).carrier) (fun j => (R j).carrier)
          Finset.univ hP href (balanced A)

/-- One extra unit of envelope slack makes the target exponent less than
half the available exponent, so the integer refinement loses no headline
constant. This estimate is uniform throughout `0<alpha<=1/2`. -/
theorem section18ExponentAt_lt_half_of_inv_le {alpha x : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hx : 0 < x)
    {mu k c : Nat} (hfit : mu + 2 ≤ 2 ^ (k + c))
    (hinv : x⁻¹ ≤ (2 / alpha) ^ (2 ^ mu)) :
    section18ExponentAt c alpha k < x / 2 := by
  have ha1 : alpha ≤ 1 := by linarith
  let t := alpha ^ (2 ^ (mu + 1))
  have ht0 : 0 < t := pow_pos ha _
  have htx : t ≤ x := by
    have hsq : alpha ^ 2 ≤ alpha / 2 := by nlinarith
    have heq : t = (alpha ^ 2) ^ (2 ^ mu) := by
      dsimp [t]
      rw [pow_succ, mul_comm (2 ^ mu) 2, pow_mul]
    have hanti := inv_anti₀ (inv_pos.mpr hx) hinv
    rw [inv_inv] at hanti
    calc
      t = (alpha ^ 2) ^ (2 ^ mu) := heq
      _ ≤ (alpha / 2) ^ (2 ^ mu) := pow_le_pow_left₀ (by positivity) hsq _
      _ = ((2 / alpha) ^ (2 ^ mu))⁻¹ := by rw [← inv_pow, inv_div]
      _ ≤ x := hanti
  have htquarter : t ≤ 1 / 4 := by
    have he : 2 ≤ (2 : Nat) ^ (mu + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2)
        (show 1 ≤ mu + 1 by omega)
    calc
      t ≤ alpha ^ 2 := pow_le_pow_of_le_one ha.le ha1 he
      _ ≤ (1 / 2 : Real) ^ (2 : Nat) := pow_le_pow_left₀ ha.le ha2 _
      _ = 1 / 4 := by norm_num
  have htarget : section18ExponentAt c alpha k ≤ t ^ 2 := by
    have he : (2 : Nat) ^ (mu + 2) ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + c)) :=
      Nat.pow_le_pow_right (by omega) hfit
    have heq : t ^ 2 = alpha ^ ((2 : Nat) ^ (mu + 2)) := by
      have hNat : (2 : Nat) ^ (mu + 2) = 2 ^ (mu + 1) * 2 := by
        rw [show mu + 2 = (mu + 1) + 1 by omega, pow_succ]
      dsimp [t]
      rw [← pow_mul, hNat]
    exact (pow_le_pow_of_le_one ha.le ha1 he).trans_eq heq.symm
  have hmul := mul_le_mul_of_nonneg_left htquarter ht0.le
  nlinarith [htarget]

theorem theorem181IntegerAt_of_polyEnvBound {c k mu : Nat}
    (h : PolyEnvBound k mu) (hfit : mu + 2 ≤ 2 ^ (k + c)) : Theorem181IntegerAt c k := by
  apply Theorem181IntegerAt.of_function_discrepancy
  intro alpha ha ha2
  obtain ⟨beta, sigma, T, hB, hb, _, hs, _, hbi, hsi⟩ := h alpha ha ha2
  exact ⟨beta, sigma, T,
    section18ExponentAt_le_of_inv_le ha ha2 hb (by omega) hbi,
    section18ExponentAt_lt_half_of_inv_le ha ha2 hs hfit hsi, hB⟩

theorem polyGenMuT_integer_slack {k : Nat} (hk : 2 ≤ k) :
    polyGenMuT k + 2 ≤ 2 ^ (k + 2 + 7) := by
  by_cases hsmall : k < 4
  · interval_cases k <;> decide
  · have hk4 : 4 ≤ k := by omega
    have hbound := polyGenMuT_le k hk4
    have hpow : (2 : Nat) ^ (k + 2 + 7) = 512 * 2 ^ k := by
      rw [show k + 2 + 7 = k + 9 by omega, pow_add]
      norm_num <;> ring
    rw [hpow]
    have hpos : 0 < (2 : Nat) ^ k := pow_pos (by omega) _
    omega

/-- Genuine integer progressions at every degree at least four, keeping
the improved `d+7` exponent as well as the discrepancy bound. -/
theorem theorem_18_1_integer_d7_four_le {d : Nat} (hd : 4 ≤ d) :
    Theorem181IntegerAt 7 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  obtain ⟨k, hk, rfl⟩ : ∃ k : Nat, 2 ≤ k ∧ d = k + 2 :=
    ⟨d - 2, by omega, by omega⟩
  apply theorem181IntegerAt_of_polyEnvBound
  · exact polyEnvBound_allT
      (fun l => ⌈multiaffinePartitionK (l + 1) (2 ^ (l + 1))⌉₊)
      (fun l => (l + 1) * multiaffinePartitionP (l + 1) (2 ^ (l + 1)))
      (fun l => two_le_ceil_multiaffinePartitionK (l + 1) (2 ^ (l + 1)))
      (fun l => Nat.mul_pos (Nat.succ_pos l) (multiaffinePartitionP_pos _ _))
      (fun l _ => section16RecurrenceProfileWith_explicit l)
      (fun l => explicit_family_constants_le l) hpp hp hK hpB k hk
  · exact polyGenMuT_integer_slack hk

/-- The cubic base also has enough slack for genuine integer progressions
at an offset below the printed `3+10`. -/
theorem theorem_18_1_integer_three : Theorem181IntegerAt 4 3 := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem181IntegerAt_of_polyEnvBound
    (polyEnvBound_three_of_phase_partition hpp hp hK hpB) (by norm_num)

end LeanProofs.GowersSzemeredi
