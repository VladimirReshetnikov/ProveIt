import DiophantineConsistency.ArithmeticTilingWord
import DiophantineConsistency.Compact44.CompactWordDefinability
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactHaltWord
open DiophantineConsistency
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_compact_word (T w H : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)
    (hw : 2 * T + 5 ≤ w) (hH : T + 2 ≤ H) (hH4 : 4 ≤ H) :
    (𝚺₁-Function₁ (fun j => CompactTableLookup.rowLookup (ArithmeticTilingBand.word T w H j))) ∧
      CompactMarkedTransport.CompactWord
        (fun j => CompactTableLookup.rowLookup (ArithmeticTilingBand.word T w H j)) (w * H) w := by
  letI : 𝚺₁-Function₁ (ArithmeticTilingBand.word T w H) :=
    ArithmeticTilingBand.word_definable T w H
  exact ⟨CompactWordDefinability.forward_composition (ArithmeticTilingBand.word T w H),
    CompactMarkedTransport.forward_marked_word (ArithmeticTilingWord.marked_word hT hw hH hH4)⟩
#print axioms CompactHaltWord.halt_compact_word
end CompactHaltWord
