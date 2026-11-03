import CompactHaltPackedWord
import CompactBaseLowNoCarry
import CompactPulsePackedCell

/-! The actual halt-derived outer word has base and pulsed low-mask-safe
cells. Product, block and high-mask conditions remain separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltWordLow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPackingBlocks
open CompactMarkedTransport CompactPackedCell CompactUniformPackedCell CompactConstructedWord
open CompactHaltPackedWord CompactBaseLowNoCarry CompactPulsePackedCell
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- In each model, the halt-derived outer word really contains the stated
zero-dummy cell at each valid index; that cell and its single dummy pulse do
not carry against the exact symbolic compact low mask. -/
theorem halt_word_low (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∀ j < haltLength T,
      let x := dig (67*8807) (haltPacked T (fun _ => 0)) j
      x = packedCell (haltRow T j) 0 ∧
      NoCarry x CompactConcreteIncrement.mask ∧
      NoCarry (x + Exp.exp (67*1063)) CompactConcreteIncrement.mask := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  have h := halt_packed_word T (fun _ => 0) hT
  letI : 𝚺₁-Function₁ (haltRow T) := h.1
  letI : 𝚺₁-Function₁ (fun t => normalizedCell (haltRow T t) 0) :=
    word_definable (haltRow T) (fun _ => 0)
  have hw := h.2.1
  intro j hj
  have he : dig (67*8807) (haltPacked T (fun _ => 0)) j = packedCell (haltRow T j) 0 := by
    change dig (67*8807) (bsum (67*8807) (fun t => normalizedCell (haltRow T t) 0) (haltLength T)) j = _
    rw [dig_bsum (fun t _ => word_cell_lt (haltRow T) (fun _ => 0) t) hj]
    exact normalizedCell_eq (haltRow T j) 0 (by simp)
  have hn := base_noCarry (haltRow T j) (hw.tile_ne j hj)
  have hp := packedCell_pulse_noCarry (haltRow T j) hn
  exact ⟨he, by rw [he]; exact hn, by rw [he]; exact hp⟩

#print axioms CompactHaltWordLow.halt_word_low
end CompactHaltWordLow
