import DiophantineConsistency.Compact44.CompactMarkedTransport
import DiophantineConsistency.Compact44.CompactForwardCellInputs

/-! SOURCE-ONLY DRAFT: uncompiled. Rebuild `CompactForwardCellInputs` on the
same marked-suffix provider as `CompactMarkedTransport` before compiling this
client. This attempts only the uniform row-to-local-aggregate bridge. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactWordCellClient
open DiophantineConsistency ArithmeticStandardCasts ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticWangTable
open CompactRowTransport CompactMarkedTransport CompactForwardCellInputs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Payload computed directly from the four fields used by `CompactWord`. -/
def payload (a : V) : V := CompactTilePayload.value
  (compactField (fun t => t.1) a) (compactField (fun t => t.2.1) a)
  (compactField (fun t => t.2.2.1) a) (compactField (fun t => t.2.2.2) a)

instance field_zero_definable (f : Quad → ℕ) : 𝚺₀-Function₁[V] (compactField f) :=
  (tab_defined (Compact943Data.rows.map f) 0).to_definable

instance field_one_definable (f : Quad → ℕ) : 𝚺₁-Function₁[V] (compactField f) :=
  (field_zero_definable f).of_zero

theorem payload_definable : 𝚺₁-Function₁[V] payload := by
  unfold payload CompactTilePayload.value
  definability

theorem word_payload_definable (b : V → V) [𝚺₁-Function₁ b] :
    𝚺₁-Function₁ (fun j => payload (b j)) := by
  letI : 𝚺₁-Function₁[V] payload := payload_definable
  definability

/-- A finite table row agrees with each corresponding model lookup. -/
theorem field_row (f : Quad → ℕ) (hf : f (0,0,0,0) = 0) (i : Fin 943) :
    compactField f (i.val : V) = ((f (Compact943Data.row i)) : V) := by
  rw [compactField_cast f hf]
  have hi : i.val < Compact943Data.rows.length := by
    simpa only [Compact943Data.rows_length] using i.isLt
  simp only [List.getElem?_toArray, getElem?_pos Compact943Data.rows i.val hi,
    Option.getD_some]
  rfl

theorem payload_row (i : Fin 943) : payload (i.val : V) = Compact943Decoder.tileValue i := by
  unfold payload Compact943Decoder.tileValue
  rw [field_row (fun t => t.1) rfl, field_row (fun t => t.2.1) rfl,
    field_row (fun t => t.2.2.1) rfl, field_row (fun t => t.2.2.2) rfl]

def wordSelector (b : V → V) (i : Fin 943) (j : V) : V := selector (b j) i
def wordPayloadBit (b : V → V) (i : Fin 41) (j : V) : V := payloadBit (payload (b j)) i

/-- The indicator function at any fixed selector position is uniformly
Σ₁-definable when the word is. -/
theorem word_selector_definable (b : V → V) [𝚺₁-Function₁ b] (i : Fin 943) :
    𝚺₁-Function₁ (wordSelector b i) := by
  have hR : 𝚺₁.Definable (fun v : Fin 2 → V =>
      (b (v 1) = (i.val : V) ∧ v 0 = 1) ∨
      (b (v 1) ≠ (i.val : V) ∧ v 0 = 0)) := by definability
  apply hR.of_iff
  intro v
  unfold wordSelector selector
  by_cases h : b (v 1) = (i.val : V) <;> simp [h]

theorem word_payload_bit_definable (b : V → V) [𝚺₁-Function₁ b] (i : Fin 41) :
    𝚺₁-Function₁ (wordPayloadBit b i) := by
  letI : 𝚺₁-Function₁[V] payload := payload_definable
  unfold wordPayloadBit payloadBit
  simp_rw [fbit_eq_div, cast_exp]
  definability

/-- Uniform bounded-cell aggregate, using the word's own four field
lookups. The word matching and marker properties are not used here. -/
theorem word_occupied {b : V → V} {N s : V} (hword : CompactWord b N s)
    {j : V} (hj : j < N) :
    (∑ i, ((CompactCoefficientMass.selector (Compact943Data.row i) : ℕ) : V) * wordSelector b i j) +
      (∑ i, ((2^(10+i.val) : ℕ) : V) * wordPayloadBit b i j) = 1 + Exp.exp 51 := by
  obtain ⟨i, hi, hsum⟩ := bounded_row_occupied (hword.tile_lt j hj)
  have hp : payload (b j) = Compact943Decoder.tileValue i := by rw [hi, payload_row]
  simpa only [wordSelector, wordPayloadBit, hp] using hsum

#print axioms CompactWordCellClient.payload_definable
#print axioms CompactWordCellClient.word_payload_definable
#print axioms CompactWordCellClient.payload_row
#print axioms CompactWordCellClient.word_selector_definable
#print axioms CompactWordCellClient.word_payload_bit_definable
#print axioms CompactWordCellClient.word_occupied
end CompactWordCellClient
