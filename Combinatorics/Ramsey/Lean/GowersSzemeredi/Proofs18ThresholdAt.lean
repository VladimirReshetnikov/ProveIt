import GowersSzemeredi.Proofs18GenericSzemeredi

/-! Parameterized final thresholds and the deduction from a discrepancy envelope.
This interface is independent of the separate polynomial-envelope theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The Theorem 18.2 threshold with `k + c` in place of the printed `k + 9`. -/
def szemerediThresholdAt (c : Nat) (delta : Real) (k : Nat) : Real :=
  (2 : Real) ^
    ((2 : Real) ^
      (delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))

/-- Theorem 18.2 at length `k` with the threshold `szemerediThresholdAt c`. -/
def Theorem182AtSharp (c k : Nat) : Prop :=
  ∀ (delta : Real) (N : Nat), 0 < delta → delta ≤ 1 / 2 →
    szemerediThresholdAt c delta k ≤ N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A k

/-- At `c = 9` it is the catalogue's Theorem 18.2 at length `k`. -/
theorem theorem182AtSharp_nine_iff (k : Nat) : Theorem182AtSharp 9 k ↔ Theorem182At k :=
  Iff.rfl

theorem double_exp_le_szemerediThresholdAt {L μ c : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThresholdAt c delta L := by
  obtain ⟨ha0, -, -, hXu⟩ := intervalUniformityParameter_gen_bounds hL hδ hδhalf
  set u : Real := delta⁻¹ with hu'
  have hu : 2 ≤ u := by rw [hu', ← one_div, le_div_iff₀ hδ]; linarith
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  set q : Nat := 2 ^ (μ + 2 * L + 13) with hq
  set E : Nat := 2 ^ (2 ^ (L + c)) with hE
  have hqE : q + 2 ≤ E := by
    have h2 : 2 ^ (μ + 2 * L + 14) = 2 * 2 ^ (μ + 2 * L + 13) := by
      rw [show μ + 2 * L + 14 = (μ + 2 * L + 13) + 1 by ring, pow_succ]; ring
    have h3 : 2 ≤ 2 ^ (μ + 2 * L + 13) :=
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1 : q + 2 ≤ 2 ^ (μ + 2 * L + 14) := by rw [hq]; omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) hfit)
  have habsorb : (2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)) ≤ u ^ q := by
    have h := pow_le_pow_left₀ (by positivity) hXu (2 ^ (μ + 9))
    rw [← pow_mul, ← pow_add] at h
    rw [hq, show μ + 2 * L + 13 = 2 * L + 4 + (μ + 9) by ring]
    exact h
  have hx1 : 1 ≤ u ^ q := one_le_pow₀ hu1
  have hinner : 1 + 2 * u ^ q ≤ u ^ E := by
    calc
      _ ≤ u ^ q * 4 := by linarith only [hx1]
      _ ≤ u ^ q * u ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hu] : (4 : Real) ≤ u ^ 2) (by positivity)
      _ = u ^ (q + 2) := (pow_add u q 2).symm
      _ ≤ _ := pow_le_pow_right₀ hu1 hqE
  have hexp : Real.exp (Real.exp (u ^ q)) ≤ (2 : Real) ^ ((2 : Real) ^ (u ^ E)) := by
    apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      2 * Real.exp (u ^ q) ≤ 2 * (2 : Real) ^ (2 * u ^ q) :=
        mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
      _ = (2 : Real) ^ (1 + 2 * u ^ q) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner
  refine (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans (hexp.trans (le_of_eq ?_))
  unfold szemerediThresholdAt
  rw [hE, ← hu']
  simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]

theorem theorem182AtSharp_of_envBound {L μ c : Nat} (hL : 3 ≤ L) (henv : EnvBound (L - 2) μ)
    (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Theorem182AtSharp c L := by
  intro delta N hδ hδhalf hN A hA hcard
  obtain ⟨ha0, haδ, -, -⟩ := intervalUniformityParameter_gen_bounds (by omega : 1 ≤ L) hδ hδhalf
  have ha2 : intervalUniformityParameter delta L ≤ 1 / 2 := haδ.trans hδhalf
  obtain ⟨beta, sigma, T, hB, b0, b1, s0, -, bi, si, Ti⟩ := henv _ ha0 ha2
  have hclosed := closedThreshold_le_of_env (by omega : 1 ≤ L) hδ hδhalf hμ hLμ b0 b1 s0 bi si Ti
  have hsrc := double_exp_le_szemerediThresholdAt (by omega : 1 ≤ L) hδ hδhalf hfit
  exact FunctionDiscrepancyBound.natural_szemeredi_closed (k := L) (by omega) hδ b0 s0 hB N
    ((hclosed.trans hsrc).trans hN) A hA hcard

end LeanProofs.GowersSzemeredi
