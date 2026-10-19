import BusyBeaver.ZFC.ControlCatalogueRotation240
import BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240

set_option autoImplicit false

/-!
The represented whole frame for the exact Rotation240 control catalogue.
The externally fixed nine-field syntax contains arbitrary internal values,
gap and extra-spare count. The live state is 85, the PC margin is 64, and
the spare tail consists of 167+extra value-one blocks. This unit supplies
the Sigma1 relation needed for internal simulation, not a simulation theorem.
It reuses the catalogue-independent arithmetic file and pure tape encodings.
Attribution of Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt is retained.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile
open ArithmeticControlTable (lookupValue lookupDef compactRows compact_lookup_at
  compact_lookup_supported opcodeValue opcodeDef opRows)
open ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 (registerBlock registerBlockDef)
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open ControlCatalogueRotation240

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Only the list of field positions is external; its values are internal. -/
noncomputable def blocksValue : List (Fin 9) → V → V → V
  | [], _, suffix => suffix
  | i::indices, file, suffix =>
      registerBlock (regValue file i) (blocksValue indices file suffix)

def blocksDef : List (Fin 9) → 𝚺₁.Semisentence 3
  | [] => .mkSigma “out file suffix. out=suffix”
  | i::indices => .mkSigma
      “out file suffix. ∃ tail, !(blocksDef indices) tail file suffix ∧
        ∃ value, !(projectionDef 8 i) value file ∧ !registerBlockDef out value tail”

instance blocks_defined (indices : List (Fin 9)) :
    𝚺₁-Function₂[V] (blocksValue indices) via blocksDef indices := by
  induction indices with
  | nil => exact .mk fun e => by simp [blocksDef, blocksValue]
  | cons i indices ih =>
      exact .mk fun e => by
        simp [blocksDef, blocksValue, regValue, (projection_defined 8 i).iff, ih.iff]

theorem blocks_list (indices : List (Fin 9)) (file suffix : V) :
    blocksValue indices file suffix = fileTape (indices.map (regValue file)) suffix := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [blocksValue, List.map_cons, fileTape, ih]

noncomputable def physicalValues (file : V) : List V := List.ofFn (regValue file)

theorem physicalValues_length (file : V) : (physicalValues file).length = 9 := by
  simp only [physicalValues, List.length_ofFn]

theorem blocks_full (file suffix : V) :
    blocksValue (List.finRange 9) file suffix = fileTape (physicalValues file) suffix := by
  rw [blocks_list, physicalValues, List.ofFn_eq_map]

theorem physicalValues_getD (file : V) (r : Fin 9) :
    (physicalValues file).getD r.val 0 = regValue file r := by
  have hr : r.val < (physicalValues file).length := by
    simpa only [physicalValues_length] using r.isLt
  rw [←List.getElem_eq_getD (h := hr) (0 : V)]
  simp only [physicalValues, List.getElem_ofFn]

noncomputable def spareValue (extra : V) : V := oneBlocks (167+extra) 0
def spareDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out extra. !oneBlocksDef out (167+extra) 0”

instance spare_defined : 𝚺₁-Function₁[V] spareValue via spareDef :=
  .mk fun e => by simp [spareDef, spareValue, numeral_eq_natCast]

/-- The last selected zero always has a following ordinary register block. -/
theorem spare_nonempty (extra : V) :
    spareValue extra = registerBlock 1 (oneBlocks (166+extra) 0) := by
  rw [spareValue, show (167+extra : V) = (166+extra)+1 by ring,
    oneBlocks_succ, registerBlock_one]

def pcRows : List (Nat × Nat) :=
  List.ofFn (fun i : Control => (sourcePC i, sourcePC i))

noncomputable def pcValue (q : V) : V := lookupValue (compactRows 0 pcRows) q 0
def pcDef : 𝚺₀.Semisentence 2 := .mkSigma
  “out q. !(lookupDef (compactRows 0 pcRows)) out q 0”

instance pc_defined : 𝚺₀-Function₁[V] pcValue via pcDef :=
  .mk fun e => by simp [pcDef, pcValue]

@[simp] theorem pc_at (i : Control) :
    pcValue (V := V) (number i : V) = (sourcePC i : V) := by
  have h := compact_lookup_at (V := V) pcRows 0 i.val
    (by simpa only [pcRows, List.length_ofFn] using i.isLt) 0
  simpa only [pcValue, pcRows, number, Nat.zero_add, List.getElem_ofFn, ite_self] using h

/-- Fixed-margin encoding of the actual dispatch boundary. -/
noncomputable def entryValue (q file extra gap : V) : V :=
  frame 85 1 (pcValue q + bitPrefix false (64 : V)
    (bitPrefix false gap (2*blocksValue (List.finRange 9) file (spareValue extra)+1)))

def entryDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out q file extra gap. ∃ pc, !pcDef pc q ∧ ∃ spares, !spareDef spares extra ∧
    ∃ blocks, !(blocksDef (List.finRange 9)) blocks file spares ∧
    ∃ gapBits, !(bitPrefixDef false) gapBits gap (2*blocks+1) ∧
    ∃ pcBits, !(bitPrefixDef false) pcBits 64 gapBits ∧
    ∃ tape, !ArithmeticCantor.pairDef tape 1 (pc+pcBits) ∧
    !ArithmeticCantor.pairDef out 85 tape”

instance entry_defined : 𝚺₁-Function₄[V] entryValue via entryDef :=
  .mk fun e => by simp [entryDef, entryValue, frame, numeral_eq_natCast, Nat.cast_ofNat]

theorem entry_at (i : Control) (file extra gap : V) :
    entryValue (number i : V) file extra gap =
      frame 85 1 (ArithmeticControlTable.binaryValue (source i).1 +
        bitPrefix false (64 : V) (bitPrefix false gap
          (2*fileTape (physicalValues file) (oneBlocks (167+extra) 0)+1))) := by
  rw [entryValue, pc_at, sourcePC_cast, blocks_full, spareValue]

private theorem opcode_supported_rows (rl : List ArithmeticControlBisim.Row)
    (q : V) (hq : opcodeValue rl q ≠ 0) :
    ∃ i : Nat, i < rl.length ∧ q = ((i+1 : Nat) : V) := by
  obtain ⟨i, hi, he⟩ := compact_lookup_supported (V := V) (opRows rl) 0 q 0 hq
  exact ⟨i, by simpa only [opRows, List.length_map] using hi,
    by simpa only [Nat.zero_add] using he⟩

theorem opcode_supported (q : V) (hq : opcodeValue table q ≠ 0) :
    ∃ i : Control, q = (number i : V) := by
  obtain ⟨i, hi, he⟩ := opcode_supported_rows table q hq
  have hi' : i < 6455 := by
    simpa only [table_length] using hi
  exact ⟨⟨i, hi'⟩, by simpa only [number, Nat.zero_add] using he⟩

/-- Both witnesses are internal. Invalid logical controls are excluded. -/
def Related (logical binary : V) : Prop :=
  logical ≠ 0 ∧ opcodeValue table (controlValue logical) ≠ 0 ∧
    ∃ extra gap : V,
      binary = entryValue (controlValue logical) (fileCodeValue logical) extra gap

def relatedDef : 𝚺₁.Semisentence 2 := .mkSigma
  “logical binary. logical≠0 ∧
    ∃ control, !controlDef control logical ∧ ∃ file, !fileCodeDef file logical ∧
    ∃ opcode, !(opcodeDef table) opcode control ∧ opcode≠0 ∧
    ∃ extra, ∃ gap, !entryDef binary control file extra gap”

theorem related_iff (logical binary : V) :
    relatedDef.val.Evalb ![logical, binary] ↔ Related logical binary := by
  simp [relatedDef, Related]

instance related_defined : 𝚺₁-Relation[V] Related via relatedDef :=
  .mk fun e => by simp [relatedDef, Related]

instance related_definable : 𝚺₁-Relation[V] Related :=
  HierarchySymbol.Defined.to_definable relatedDef related_defined

theorem related_live (logical binary : V) (h : Related logical binary) : logical ≠ 0 := h.1

theorem entry_active (q file extra gap : V) : first (entryValue q file extra gap) ≠ 0 := by
  simp [entryValue, frame]

theorem related_active (logical binary : V) (h : Related logical binary) : first binary ≠ 0 := by
  obtain ⟨_, _, extra, gap, rfl⟩ := h
  exact entry_active _ _ extra gap

end SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240
