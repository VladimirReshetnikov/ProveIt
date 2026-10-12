import GowersSzemeredi.Proofs16IntegerBoxFactors
import GowersSzemeredi.Proofs18NaturalIntervalIncrement

/-! The uncapped loss quantifier is impossible even for genuine integer
boxes. This refutation is separate from the corrected cover statements. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private def integerBinaryBox : Box 2 1 where
  axis := fun _ => ⟨0, 1, 2⟩
  commonDiff := 1
  axis_step := fun _ => rfl

private theorem integerBinaryBox_genuine : integerBinaryBox.HasIntegerRepresentatives := by
  let A (_ : Fin 1) : NatAP := ⟨0, 1, 2⟩
  apply Box.IsAscendingInteger.toGenuine
  refine ⟨1, A, Nat.one_pos, by simp only [Nat.cast_one, integerBinaryBox], fun i => ?_⟩
  refine ⟨NatAP.isProper_of_step_pos _ Nat.one_pos, rfl, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    simpa only [A, zero_add, mul_one] using Finset.mem_range.mpr j.isLt
  · simp only [A, NatAP.toModAP, integerBinaryBox, Nat.cast_zero, Nat.cast_one]

theorem multipleLinearity_uncapped_integer_loss_counterexample :
    ¬ (∀ eta : Real, 0 < eta → ∀ P : Box 2 1, P.HasIntegerRepresentatives →
      ∃ M : Nat, ∃ Q : Fin M → Box 2 1,
        IsBoxPartition Q P ∧ (∀ j, (Q j).HasIntegerRepresentatives) ∧
        ∀ j, (P.width : Real) ^ multipleC eta 1 1 ≤ (Q j).width) := by
  intro h
  have hx : (fun _ : Fin 1 => (0 : ZMod 2)) ∈ integerBinaryBox.carrier := by
    simp [integerBinaryBox, Box.carrier, ModAP.carrier]
  obtain ⟨M, Q, hpart, hQ, hwidth⟩ := h 2 (by norm_num) integerBinaryBox integerBinaryBox_genuine
  obtain ⟨j, _⟩ := (hpart.1 _).mp hx
  have hcap : ((Q j).width : Real) ≤ 2 := by
    exact_mod_cast (Q j).width_le_modulus (hQ j).isProper
  have hc : (2 : Real) ≤ multipleC 2 1 1 := by
    unfold multipleC
    simp only [one_mul]
    have hE : 1 ≤ (2 : Nat) ^ ((2 : Nat) ^ (1 + 8)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hE
  have hfour : (4 : Real) ≤ (2 : Real) ^ multipleC 2 1 1 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hc
    simpa only [show (2 : Real) ^ (2 : Real) = 4 by norm_num] using hpow
  have hPwidth : integerBinaryBox.width = 2 := by simp [integerBinaryBox, Box.width]
  have hlow := hwidth j
  rw [hPwidth] at hlow
  change (2 : Real) ^ multipleC 2 1 1 ≤ (Q j).width at hlow
  linarith only [hlow, hfour, hcap]

end LeanProofs.GowersSzemeredi
