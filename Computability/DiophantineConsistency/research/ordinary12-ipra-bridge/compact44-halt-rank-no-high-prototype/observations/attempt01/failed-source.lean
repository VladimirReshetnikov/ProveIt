import CompactHaltRankHighFields
import CompactMarkedAllHigh
import CompactHighOriginMarked
import CompactPackingGeometry

/-! All physical high-mask premises for the halt-to-rank bridge are derived. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltRankNoHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactRankVariation
open CompactConstructedWord CompactWordPulseEquality CompactHaltPackedWord
open CompactHaltRankHighFields CompactMarkedAllHigh CompactHighOriginMarked
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A model-internal halt yields a definable selected pulse with physical
packing and calibrated rank. No high-mask hypotheses remain. -/
theorem halt_chosen_rank_no_high (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) ∧
      PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask (highNat : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ) ∧
      windowRank (paramKernel rho : V) (haltLength T) (haltStride T) c
        (perturb (baseCell (haltRow T)) δ) % (590069 * haltLength T) =
        (590069 * haltStride T) % (590069 * haltLength T) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  have hword := halt_packed_word T (fun _ => 0) hT
  letI : 𝚺₁-Function₁ (haltRow T) := hword.1
  have hw := hword.2.1
  have hg := CompactPackingGeometry.geometry T
  have hspos : 0 < haltStride T := power_pos _ _ (by norm_num)
  have he0 : cellWord (haltRow T) (fun _ => 0) = baseCell (haltRow T) := by
    funext j
    have h := cellWord_boolean_pulse (haltRow T) (fun _ => 0) j (by simp)
    simpa only [mul_zero, add_zero] using h
  have hall0 := marked_all_high (haltRow T) (fun _ => 0) hw hg.1 hg.2 (by intro j; simp)
  rw [he0] at hall0
  have hbase := base_high_fields hw hspos hg.2 hall0
  have hb : HighMaskFields 590069 (paramKernel rho : V) (highNat : V)
      (haltLength T) (haltStride T) (baseCell (haltRow T)) := ⟨hbase.1, hbase.2⟩
  have hp : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) →
      HighMaskFields 590069 (paramKernel rho : V) (highNat : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ) := by
    intro δ hd hbool _
    letI : 𝚺₁-Function₁ δ := hd
    have he : cellWord (haltRow T) δ = pulsedCell (haltRow T) δ := by
      funext j
      exact cellWord_boolean_pulse (haltRow T) δ j (hbool j)
    have hall := marked_all_high (haltRow T) δ hw hg.1 hg.2 hbool
    rw [he] at hall
    have hh := pulsed_high_fields hw hspos hg.2 hbool hall
    exact ⟨hh.1, hh.2⟩
  exact halt_chosen_rank_high_fields T c hT hb hp

#print axioms CompactHaltRankNoHigh.halt_chosen_rank_no_high
end CompactHaltRankNoHigh
