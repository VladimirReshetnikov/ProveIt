import GowersSzemeredi.Proofs16BoxGeometry

/-! Declarations of `Proofs16BoxGeometry` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

private def binaryFullBox : Box 2 1 where
  axis := fun _ => { start := 0, step := 1, length := 2 }
  commonDiff := 1
  axis_step := by intro _; rfl

/-- Even the width-only part of multiple linearity is impossible if its
loss parameter is allowed to be arbitrarily large. -/
theorem multipleLinearity_uncapped_loss_counterexample :
    ¬ (∀ eta : Real, 0 < eta → ∀ P : Box 2 1, P.IsProper →
      ∃ M : Nat, ∃ Q : Fin M → Box 2 1,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        ∀ j, (P.width : Real) ^ (multipleC eta 1 1) ≤ (Q j).width) := by
  intro h
  have hP : binaryFullBox.IsProper := by
    intro i
    norm_num [binaryFullBox, ModAP.IsProper, ModAP.carrier]
    change ((Finset.univ : Finset (Fin 2)).image (fun j => (j.val : ZMod 2))).card = 2
    rw [Finset.univ_fin2]
    norm_num
  have hx : (fun _ : Fin 1 => (0 : ZMod 2)) ∈ binaryFullBox.carrier := by
    simp [binaryFullBox, Box.carrier, ModAP.carrier]
  obtain ⟨M, Q, hpart, hproper, hwidth⟩ := h 2 (by norm_num) binaryFullBox hP
  obtain ⟨j, _⟩ := (hpart.1 _).mp hx
  have hbound : ((Q j).width : Real) ≤ 2 := by exact_mod_cast (Q j).width_le_modulus (hproper j)
  have hc : (2 : Real) ≤ multipleC 2 1 1 := by
    unfold multipleC
    simp only [one_mul]
    have hE : 1 ≤ (2 : Nat) ^ ((2 : Nat) ^ (1 + 8)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hE
  have hfour : (4 : Real) ≤ (2 : Real) ^ multipleC 2 1 1 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hc
    norm_num at hpow ⊢
    exact hpow
  have hw := hwidth j
  have hwidthP : binaryFullBox.width = 2 := by simp [binaryFullBox, Box.width]
  rw [hwidthP] at hw
  norm_num at hw
  linarith

end LeanProofs.GowersSzemeredi
