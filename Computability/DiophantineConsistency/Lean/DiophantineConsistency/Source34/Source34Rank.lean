import DiophantineConsistency.Source34.Source34Origin
import DiophantineConsistency.Mixed121.Mixed121Rank
import DiophantineConsistency.Source34.Source34Calibration
import DiophantineConsistency.Compact44.ArithmeticConstructionVariationCompact44
import DiophantineConsistency.Compact44.CompactHaltWord

/-! # A halting run gives a calibrated packing, at the source34 ports

`Mixed121Rank` at the source34 tuple. The rank-variation layer
(`Mixed121Rank.windowRank`, `rank_variation`, `calibrated_rank`,
`ProductBlockInput`, `packing_of_pulse`) is generic in the kernel and masks and
is used directly; `Source34ConstructionUnit.Gamma` and
`Mixed121ConstructionUnit.Gamma` have the same body, so the source34
calibration feeds `calibrated_rank` by unfolding.

`halt_chosen_rank_no_high`: from an internal halt of machine 215 at time `T`,
the halt word at `N = λ^(2T+4)`, `w = λ^(T+1)` has a Boolean, `𝚺₁` controller
choice `δ` (`Source34Calibration.chosen_calibration`) such that the perturbed
word is a full `PackingInput` at the source34 ports and its window rank is
`d·w (mod d·N)`. Every packing field is discharged:

* the products and cell sums (`Source34Cell`, `Source34Column`);
* the low fields (`Source34Word`);
* the high fields, through the whole high mask (`Source34High`,
  `Source34Origin`);
* the mask scalars (`Source34Ports`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34Rank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPacking ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticConstructionVariationCompact44 (variation rank_shift)
open DiophantineConsistency.Source34ConstructionUnit (Gamma)
open Mixed121Kernel (rho)
open Mixed121Rank (windowRank rank_variation calibrated_rank ProductBlockInput packing_of_pulse)
open Mixed121Column (perturb perturb_definable)
open Mixed121Word (haltRow haltLength haltStride)
open CompactMarkedTransport Source34Kernel Source34Cell Source34Word Source34Block Source34Column
  Source34High Source34Origin
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho Source34Ports.lowNat Source34Ports.highNat
  Source34Ports.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The chosen controller at the halt dimensions -/

theorem chosen_rank_of_pulse (T MC HP c : V) {X0 : V → V} [𝚺₁-Function₁ X0]
    (h0 : PackingInput 1064921 (paramKernel rho : V) MC HP
      (power 2341 ((2*T+3)+1)) (power 2341 (T+1)) X0)
    (hpulse : ∀ j < power 2341 ((2*T+3)+1), 0 < j →
      NoCarry (X0 j + Exp.exp (121*1063)) MC)
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 2341 ((2*T+3)+1) ∧
        j + power 2341 (T+1) < power 2341 ((2*T+3)+1)) →
      ProductBlockInput 1064921 (paramKernel rho : V) HP
        (power 2341 ((2*T+3)+1)) (power 2341 (T+1)) (perturb X0 δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 2341 ((2*T+3)+1) ∧
        j + power 2341 (T+1) < power 2341 ((2*T+3)+1)) ∧
      PackingInput 1064921 (paramKernel rho : V) MC HP
        (power 2341 ((2*T+3)+1)) (power 2341 (T+1)) (perturb X0 δ) ∧
      windowRank (paramKernel rho : V) (power 2341 ((2*T+3)+1))
        (power 2341 (T+1)) c (perturb X0 δ) % (1064921 * power 2341 ((2*T+3)+1)) =
          (1064921 * power 2341 (T+1)) % (1064921 * power 2341 ((2*T+3)+1)) := by
  obtain ⟨δ, hδd, hδb, hδs, hcal⟩ := Source34Calibration.chosen_calibration T
    (windowRank (paramKernel rho : V) (power 2341 ((2*T+3)+1)) (power 2341 (T+1)) c X0)
  letI : 𝚺₁-Function₁ δ := hδd
  have h1 := packing_of_pulse h0 hδb (fun j hj => (hδs j hj).1) hpulse (hblocks δ hδd hδb hδs)
  have hX : ∀ j < power 2341 ((2*T+3)+1),
      perturb X0 δ j = X0 j + Exp.exp (121*1063) * δ j := fun j _ => rfl
  have hs : ∀ j, δ j ≠ 0 → j+1 < power 2341 ((2*T+3)+1) ∧
      j+power 2341 (T+1) < power 2341 ((2*T+3)+1) :=
    fun j hj => ⟨(hδs j hj).2.1, (hδs j hj).2.2⟩
  exact ⟨δ, hδd, hδb, hδs, h1, calibrated_rank h0 h1 hX hδb hs hcal⟩

theorem baseCell_definable (row : V → V) [𝚺₁-Function₁ row] :
    𝚺₁-Function₁ (baseCell row) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  have hd := word_definable row (fun _ => (0 : V))
  have he : (fun j => normalizedCell (row j) (0 : V)) = baseCell row := by
    funext j
    exact normalizedCell_eq (row j) 0 (by simp)
  rw [he] at hd
  exact hd

theorem masks : ((Source34Ports.lowNat : ℕ) : V)+1 < Exp.exp 1064921 ∧
    1 ≤ ((Source34Ports.highNat : ℕ) : V) ∧ ((Source34Ports.highNat : ℕ) : V) < Exp.exp 1064921 := by
  have hβ : ((Source34Ports.betaNat : ℕ) : V) + 1 = Exp.exp 1064921 := by
    have h := Source34Ports.beta_identity (V:=V)
    rwa [show (121:V)*8801 = 1064921 by norm_num] at h
  have hL : ((Source34Ports.lowNat : ℕ) : V) < ((Source34Ports.betaNat : ℕ) : V) := by
    exact_mod_cast Source34Ports.low_lt_beta
  have hH : ((Source34Ports.highNat : ℕ) : V) < ((Source34Ports.betaNat : ℕ) : V) := by
    exact_mod_cast Source34Ports.high_lt_beta
  have h1 : 1 ≤ ((Source34Ports.highNat : ℕ) : V) := by
    exact_mod_cast (le_trans (by norm_num) Source34Ports.high_pos)
  refine ⟨?_, h1, ?_⟩
  · rw [← hβ]
    simpa only [add_comm] using add_lt_add_right hL 1
  · rw [← hβ]
    exact lt_trans hH (lt_add_one _)

/-! ## The halt word -/

/-- An internal halt gives a calibrated, fully packed perturbed halt word. -/
theorem halt_chosen_rank_no_high (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) ∧
      PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V)
        ((Source34Ports.highNat : ℕ) : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ) ∧
      windowRank (paramKernel rho : V) (haltLength T) (haltStride T) c
        (perturb (baseCell (haltRow T)) δ) % (1064921 * haltLength T) =
        (1064921 * haltStride T) % (1064921 * haltLength T) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  obtain ⟨hrow, hw, -⟩ := halt_packed_word T (fun _ => (0:V)) hT
  letI : 𝚺₁-Function₁ (haltRow T) := hrow
  letI : 𝚺₁-Function₁ (baseCell (haltRow T)) := baseCell_definable (haltRow T)
  have hg := Mixed121Word.geometry T
  have hw0 : 0 < haltStride T := power_pos _ _ (by norm_num)
  have hm := masks (V:=V)
  set row := haltRow T
  set N := haltLength T
  set w := haltStride T
  -- base word fields
  have hzero_word : cellWord row (fun _ => (0:V)) = baseCell row := by
    funext j
    exact normalizedCell_eq (row j) 0 (by simp)
  have hall0 := marked_all_high row (fun _ => (0:V)) hw hg.1 hg.2 (fun _ => by simp)
  rw [hzero_word] at hall0
  have hnorm0 : (fun k => normalizedCell (row k) ((fun _ => (0:V)) k)) = baseCell row := hzero_word
  have hhigh0 := normalized_high_fields (dummy := fun _ => (0:V)) hw hw0 hg.2
    (by rw [hnorm0]; exact hall0)
  rw [hnorm0] at hhigh0
  obtain ⟨ho, hlo, hlow⟩ := base_low_fields hw
  have hcells := marked_cell_sums row (fun _ => (0:V)) hw (fun _ _ => by simp)
  have h0 : PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V)
      ((Source34Ports.highNat : ℕ) : V) N w (baseCell row) :=
    ⟨hg.1, hg.2, fun j hj => packed_cell_product_lt (row j) 0 (hw.tile_ne j hj) (by simp),
      hm.1, hm.2.1, hm.2.2, hcells.1, ho, (block_pos (δ := fun _ => (0:V)) hw 0).1, hlo,
      fun j hj _ => hlow j hj, hhigh0.1, hhigh0.2⟩
  have hpulse : ∀ j < N, 0 < j →
      NoCarry (baseCell row j + Exp.exp (121*1063)) ((Source34Ports.lowNat : ℕ) : V) :=
    fun j hj _ => packedCell_pulse_noCarry (row j) (hlow j hj)
  apply chosen_rank_of_pulse T _ _ c h0 hpulse
  intro δ hd hb hs
  letI : 𝚺₁-Function₁ δ := hd
  have hcw : cellWord row δ = pulsedCell row δ := by
    funext j
    exact cellWord_boolean_pulse row δ j (hb j)
  have hall := marked_all_high row δ hw hg.1 hg.2 hb
  rw [hcw] at hall
  have hhigh := pulsed_high_fields hw hw0 hg.2 hb hall
  refine ⟨?_, (marked_cell_sums row δ hw (fun j _ => hb j)).2, (block_pos (δ := δ) hw 0).2,
    hhigh.1, hhigh.2⟩
  intro j hj
  rcases le_one_iff_eq_zero_or_one.mp (hb j) with hz | ho1
  · simpa only [perturb, baseCell, hz, mul_zero, add_zero] using
      (packed_cell_product_lt (row j) 0 (hw.tile_ne j hj) (by simp))
  · simpa only [perturb, baseCell, ho1, mul_one] using
      (packed_pulse_product_lt (row j) (hw.tile_ne j hj))

#print axioms Source34Rank.chosen_rank_of_pulse
#print axioms Source34Rank.masks
#print axioms Source34Rank.halt_chosen_rank_no_high
end Source34Rank
