import CompactUniformPackedCell

/-! Equality between the normalized dummy digit and an explicit pulse. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactCellPulseEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactCellDigit CompactCellDigitDef CompactPackedCell CompactUniformPackedCell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/- The point-indicator block-sum argument follows the existing
ArithmeticControllerDataCompact44.bsum_pt and bsum_add_pt proofs. -/
def pt (q j : V) : V := if j = q then 1 else 0

instance pt_definable (q : V) : 𝚺₁-Function₁ (pt q) := by
  have hR : 𝚺₁.Definable (fun v : Fin 2 → V =>
      (v 1 = q ∧ v 0 = 1) ∨ (v 1 ≠ q ∧ v 0 = 0)) := by definability
  apply hR.of_iff
  intro v
  unfold pt
  by_cases h : v 1 = q <;> simp [h]

theorem pt_le (q j : V) : pt q j ≤ 1 := by unfold pt; split <;> simp

theorem one_lt_exp {w : V} (hw : 0 < w) : (1 : V) < Exp.exp w := by
  have h := exp_succ (w - 1)
  rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hw)] at h
  rw [h]
  calc (1 : V) < 2 := by norm_num
    _ ≤ 2 * Exp.exp (w - 1) := le_mul_of_one_le_right (by norm_num) (one_le_exp _)

theorem bsum_pt {w : V} (hw : 0 < w) (q : V) :
    ∀ n, (q < n ∧ bsum w (pt q) n = Exp.exp (w * q)) ∨ (n ≤ q ∧ bsum w (pt q) n = 0) := by
  have hb : ∀ j, pt q j < Exp.exp w := fun j => lt_of_le_of_lt (pt_le q j) (one_lt_exp hw)
  haveI := bsum_definable w (pt q) hb
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact Or.inr ⟨Arithmetic.zero_le _, by simp⟩
  case succ n ih =>
    rw [bsum_succ (fun j _ => hb j)]
    rcases ih with ⟨hq, hs⟩ | ⟨hq, hs⟩
    · have hne : n ≠ q := ne_of_gt hq
      exact Or.inl ⟨lt_trans hq (lt_add_one n), by simp [hs, pt, hne]⟩
    · rcases lt_or_eq_of_le hq with hlt | rfl
      · have hne : n ≠ q := ne_of_lt hlt
        exact Or.inr ⟨lt_iff_succ_le.mp hlt, by simp [hs, pt, hne]⟩
      · exact Or.inl ⟨lt_add_one n, by simp [hs, pt]⟩

theorem bsum_add_pt {w : V} (hw : 0 < w) {f f' : V → V} [𝚺₁-Function₁ f] [𝚺₁-Function₁ f']
    {n q : V} (hq : q < n) (hf : ∀ j < n, f j ≤ 1) (hfq : f q = 0)
    (hf' : ∀ j < n, f' j = f j + pt q j) :
    bsum w f' n = bsum w f n + Exp.exp (w * q) := by
  have hsum : ∀ j < n, f j + pt q j < Exp.exp w := by
    intro j hj
    by_cases hjq : j = q
    · rw [hjq, hfq, zero_add]; exact lt_of_le_of_lt (pt_le q q) (one_lt_exp hw)
    · simp only [pt, hjq, if_false, add_zero]; exact lt_of_le_of_lt (hf j hj) (one_lt_exp hw)
  rw [bsum_add hsum hf']
  rcases bsum_pt hw q n with ⟨_, h⟩ | ⟨h, _⟩
  · rw [h]
  · exact absurd hq (not_lt.mpr h)

theorem cell_one (a : V) : packedCell a 1 = packedCell a 0 + Exp.exp (67*1063) := by
  letI : 𝚺₁-Function₁ (cellDigit a (0:V)) := cellDigit_definable a 0
  letI : 𝚺₁-Function₁ (cellDigit a (1:V)) := cellDigit_definable a 1
  unfold packedCell
  apply bsum_add_pt (w := (67:V)) (q := (1063:V)) (by norm_num) (by norm_num)
  · intro j _; exact cellDigit_le_one a 0 j (by simp)
  · exact dummy_digit a 0
  · intro j _
    by_cases hj : j = 1063
    · subst j
      simp [dummy_digit, pt]
    · have he : cellDigit a 1 j = cellDigit a 0 j := by simp [cellDigit, hj]
      simp [pt, hj, he]

theorem normalized_eq_pulse (a d : V) :
    normalizedCell a d = packedCell a 0 + Exp.exp (67*1063) * (d % 2) := by
  have hd : d % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt d (by norm_num))
  rcases le_one_iff_eq_zero_or_one.mp hd with h0 | h1
  · simp [normalizedCell, h0]
  · simp [normalizedCell, h1, cell_one]

#print axioms CompactCellPulseEquality.cell_one
#print axioms CompactCellPulseEquality.normalized_eq_pulse
end CompactCellPulseEquality
