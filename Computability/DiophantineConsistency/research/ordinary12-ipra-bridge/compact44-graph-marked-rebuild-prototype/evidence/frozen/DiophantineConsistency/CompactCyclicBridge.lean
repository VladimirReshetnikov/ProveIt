import DiophantineConsistency.CompactMarkedReverse
import DiophantineConsistency.CompactNoExtra
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCyclicBridge
open DiophantineConsistency CompactRelabelDraft CompactMarkedTransport CompactInverseDraft CompactRowTransport CompactTableLookup CompactMarkedReverse CompactNoExtra
open DiophantineConsistency.ArithmeticWangTable DiophantineConsistency.ArithmeticWangPlane
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A supplied compact cyclic word, without the extra-row exclusion assumed. -/
structure RawCompactWord (b : V → V) (N s : V) : Prop where
  pos : 0 < N
  tile_lt : ∀ j < N, b j < 943
  marker : b 0 = 0
  east : ∀ j < N, ∀ j' < N, (j' + 1) % N = j →
    compactField (fun t => t.2.2.1) (b j) = compactField (fun t => t.1) (b j')
  south : ∀ j < N, ∀ j' < N, (j' + s) % N = j →
    compactField (fun t => t.2.2.2) (b j) = compactField (fun t => t.2.1) (b j')

theorem upgrade_supplied_word {b : V → V} {N s : V} (h : RawCompactWord b N s) :
    CompactWord b N s := by
  exact ⟨h.pos, h.tile_lt, cyclic_excludes_extra b h.pos h.tile_lt h.east,
    h.marker, h.east, h.south⟩

theorem reverse_supplied_word {b : V → V} {N s : V} (h : RawCompactWord b N s) :
    MarkedWord (fun j => inverseLookup (b j)) N s :=
  reverse_marked_word (upgrade_supplied_word h)

/-- The lookup itself is bounded-definable. Composition with a represented
    word and internal coding remain additional proof obligations. -/
instance rowLookup_defined : 𝚺₀-Function₁[V] rowLookup :=
  (tab_defined rowIndices.toList 0).to_definable
#print axioms CompactCyclicBridge.reverse_supplied_word
#print axioms CompactCyclicBridge.rowLookup_defined
end CompactCyclicBridge
