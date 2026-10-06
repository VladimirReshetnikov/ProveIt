import GowersSzemeredi.Section16

/-!
# Geometric safeguards for multiple linearity

Proper axes identify formal lengths with cardinalities. The upper bound on
the loss parameter is also necessary: at loss 2 the printed width formula
would force a proper partition cell in ZMod 2 to have width at least 4.
-/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Width is at most the length of each axis. -/
theorem Box.width_le_axis_length {N k : Nat} (P : Box N k) (i : Fin k) :
    P.width ≤ (P.axis i).length := by
  classical
  have hk : k ≠ 0 := by have := i.isLt; omega
  simp only [Box.width, dif_neg hk]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- In a proper box width measures cardinality, not an inflated presentation. -/
theorem Box.width_le_axis_card {N k : Nat} (P : Box N k) (hP : P.IsProper)
    (i : Fin k) : P.width ≤ (P.axis i).carrier.card := by
  rw [hP i]
  exact P.width_le_axis_length i

/-- Every proper box in ZMod N has width at most N. -/
theorem Box.width_le_modulus {N k : Nat} [NeZero N] (P : Box N k)
    (hP : P.IsProper) : P.width ≤ N := by
  by_cases hk : k = 0
  · subst k
    simp [Box.width]
  · let i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    exact (P.width_le_axis_card hP i).trans (by
      simpa using Finset.card_le_univ (P.axis i).carrier)

private def binaryFullBox : Box 2 1 where
  axis := fun _ => { start := 0, step := 1, length := 2 }
  commonDiff := 1
  axis_step := by intro i; rfl

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
