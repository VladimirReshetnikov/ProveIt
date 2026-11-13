import DiophantineConsistency.Compact44.CompactHaltDimensions
import DiophantineConsistency.Compact44.CompactWordProperties

/-! From a model-internal halt construct a bounded marked compact word at
the chosen controller dimensions. No mask, product or packing assertion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltPackedWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticWindowDigits
open CompactSymbolicKernel CompactForwardCellInputs CompactWordCellClient CompactMarkedTransport
open CompactConstructedWord CompactWordProperties
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def haltRow (T j : V) : V := CompactTableLookup.rowLookup
  (ArithmeticTilingBand.word T (power 581197 (T+1)) (power 581197 (T+3)) j)

def haltLength (T : V) : V := power 581197 ((2*T+3)+1)
def haltStride (T : V) : V := power 581197 (T+1)
def haltPacked (T : V) (dummy : V → V) : V := packedWord (haltRow T) dummy (haltLength T)

/-- The halt hypothesis is interpreted inside an arbitrary IΣ₁ model. The
dummy function is supplied and represented; its values are normalized mod 2. -/
theorem halt_packed_word (T : V) (dummy : V → V) [𝚺₁-Function₁ dummy]
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    (𝚺₁-Function₁ (haltRow T)) ∧
    CompactWord (haltRow T) (haltLength T) (haltStride T) ∧
    1 ≤ haltPacked T dummy ∧
    haltPacked T dummy < Exp.exp ((67*8807)*haltLength T) ∧
    (∀ k < 8807*haltLength T, dig 67 (haltPacked T dummy) k ≤ 1) ∧
    (∀ j < haltLength T, ∀ i : Fin 943,
      dig 67 (haltPacked T dummy) (8807*j+(i.val:V)) = wordSelector (haltRow T) i j) ∧
    (∀ j < haltLength T, ∀ i : Fin 41,
      dig 67 (haltPacked T dummy) (8807*j+(position i:V)) = wordPayloadBit (haltRow T) i j) ∧
    (∀ j < haltLength T,
      dig 67 (haltPacked T dummy) (8807*j+1063) = dummy j % 2) := by
  obtain ⟨hrow, hword⟩ := CompactHaltDimensions.halt_compact_word_powers T hT
  have he := (CompactHaltDimensions.dimensions T).2.2.2
  rw [he] at hword
  change 𝚺₁-Function₁ (haltRow T) at hrow
  letI : 𝚺₁-Function₁ (haltRow T) := hrow
  have hw : CompactWord (haltRow T) (haltLength T) (haltStride T) := hword
  refine ⟨hrow, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact marked_word_origin _ _ _ _ hw
  · exact packedWord_lt _ _ _
  · exact word_cap _ _ _
  · exact word_selector _ _ _
  · exact word_copy _ _ _
  · exact word_dummy _ _ _

#print axioms CompactHaltPackedWord.halt_packed_word
end CompactHaltPackedWord
