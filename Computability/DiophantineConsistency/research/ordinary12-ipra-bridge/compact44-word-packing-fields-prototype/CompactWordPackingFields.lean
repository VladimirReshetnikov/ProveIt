import CompactWordLowFields
import DiophantineConsistency.ArithmeticPacking

/-! Pack both concrete word families from the remaining explicit fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactWordPackingFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPacking
open CompactMarkedTransport CompactWordLowFields

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The five product, block and high-mask fields still needed per word. -/
structure TransportFields (d K HP N s : V) (X : V → V) : Prop where
  hi_lt : ∀ j < N, K * X j < Exp.exp d * Exp.exp d
  cell_sum : ∀ j < N, X j + blk d K N s X j < Exp.exp d
  blk_pos : 0 < blk d K N s X 0
  high_origin : NoCarry (blk d K N s X 0) (HP - 1)
  high : ∀ j < N, 0 < j → NoCarry (blk d K N s X j) HP

/-- Both actual word families meet the full `PackingInput` interface when
the exact remaining scalar and product/block premises are provided. -/
theorem pack_from_remaining_fields {row δ : V → V} {d K HP N s : V}
    (hw : CompactWord row N s) (hbool : ∀ j, δ j ≤ 1)
    (hpos : ∀ j, δ j ≠ 0 → 0 < j)
    (hN : 1 < N) (hs : s < N)
    (hMC : (CompactConcreteIncrement.mask : V) + 1 < Exp.exp d)
    (hHPpos : 1 ≤ HP) (hHPlt : HP < Exp.exp d)
    (hbase : TransportFields d K HP N s (baseCell row))
    (hpulsed : TransportFields d K HP N s (pulsedCell row δ)) :
    PackingInput d K CompactConcreteIncrement.mask HP N s (baseCell row) ∧
    PackingInput d K CompactConcreteIncrement.mask HP N s (pulsedCell row δ) := by
  obtain ⟨ho, hlo, hlow⟩ := base_low_fields hw
  obtain ⟨hpo, hplo, hplow⟩ := pulsed_low_fields hw hbool hpos
  constructor
  · exact ⟨hN, hs, hbase.hi_lt, hMC, hHPpos, hHPlt, hbase.cell_sum, ho,
      hbase.blk_pos, hlo, fun j hj _ => hlow j hj, hbase.high_origin, hbase.high⟩
  · exact ⟨hN, hs, hpulsed.hi_lt, hMC, hHPpos, hHPlt, hpulsed.cell_sum, hpo,
      hpulsed.blk_pos, hplo, fun j hj _ => hplow j hj, hpulsed.high_origin, hpulsed.high⟩

#print axioms CompactWordPackingFields.pack_from_remaining_fields
end CompactWordPackingFields
