import BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240
import BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240

set_option autoImplicit false

/-!
Whole-tape meanings of the actual Rotation240 site start and target syntax.
The state is 85, the fixed margin is 64, and the register tail contains
167+extra value-one blocks. Increment adds one spare; positive decrement
instead contributes a separate finite padding cell. These effects are never
identified. All file values, spare counts and gaps range over an arbitrary
IΣ1 model; only the finite path and physical register positions are external.

This unit is pure numeric interpretation and consumed-path reentry algebra.
It assumes no binary runtime, proves no first exit, and asserts no complete
internal simulation or PA endpoint. Mira-Cult, Jeff Ketchersid, Andrew James
Wade and ProveIt retain their source/program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RegisterPathClean
open ArithmeticMachineUniformScansPerm252
open ArithmeticSymbolicTapePerm252 (affine)
open ArithmeticSymbolicTapeRotation240
open ArithmeticSymbolicStepRotation240 (value)
open ArithmeticSymbolicBoxesRotation240
open ArithmeticFiniteTapeRotation240 (bitsPrefix)
open ArithmeticCarryTraversalRotation240 (fileTape)
open ArithmeticOneRegisterBlocksRotation240 (oneBlocks)
open ArithmeticControlFile
open ArithmeticControlFrameDataRotation240 (physicalValues physicalValues_length
  physicalValues_getD entryValue)
open ArithmeticDispatchRebaseRotation240 (startPathValue targetPathValue budget)
open ControlCatalogueRotation240
open SymbolicRotation240 (Effect Segment Box)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def effectValues (values : List V) : Effect → List V
  | .unchanged => values
  | .increment r => writeAt values r.val (values.getD r.val 0+1)
  | .decrement r => writeAt values r.val (values.getD r.val 0-1)

def effectExtra (extra : V) : Effect → V
  | .increment _ => extra+1
  | _ => extra

theorem effectValues_length (values : List V) (effect : Effect) :
    (effectValues values effect).length = values.length := by
  cases effect <;> simp only [effectValues,writeAt_length]

theorem box_plain (values : List V) (extra suffix : V) (effect : Effect) :
    boxPrefix values extra (.plain effect) suffix =
      fileTape (effectValues values effect)
        (oneBlocks (167+effectExtra extra effect) suffix) := by
  cases effect <;> rfl

noncomputable def startValue (values : List V) (extra gap : V) (Q : List Bool) : V :=
  value values extra gap (SiteRotation240.start Q)

noncomputable def targetValue (values : List V) (extra gap : V) (P : List Bool)
    (overflow : Bool) (padExtra : Nat) (effect : Effect) : V :=
  value values extra gap (SiteRotation240.target P overflow padExtra (.plain effect))

theorem map_bits_prefix (gap : V) (boxes : Box → V → V)
    (P : List Bool) (suffix : V) :
    tapePrefix gap boxes (P.map Segment.bit) suffix = bitsPrefix P suffix := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.map_cons,tapePrefix,segmentPrefix,bitsPrefix,ih]

theorem target_format (values : List V) (extra gap : V) (P : List Bool)
    (overflow : Bool) (padExtra : Nat) (effect : Effect) :
    targetValue values extra gap P overflow padExtra effect =
      targetPathValue P overflow padExtra gap
        (2*boxPrefix values extra (.plain effect) 0+1) := by
  have hb : (if overflow then 1 else 0 : Nat) = overflow.toNat := by
    cases overflow <;> rfl
  simp only [targetValue,value,configValue,SiteRotation240.target,SiteRotation240.dispatch,
    dispatchRotation240_eq,SiteRotation240.minDistance,ArithmeticMachinePerm252.stateCode,
    if_false,tapePrefix_append,map_bits_prefix,tapePrefix,segmentPrefix,affine,digit,
    Bool.false_eq_true,if_true,mul_zero,zero_add,Nat.cast_ofNat,Nat.cast_one,
    one_mul,show ((84 : Fin 240).val+1 : Nat) = 85 by rfl,hb,targetPathValue,budget]

theorem start_format (values : List V) (extra gap : V) (P : List Bool) :
    startValue values extra gap P = startPathValue P gap
      (2*fileTape values (oneBlocks (167+extra) 0)+1) := by
  have hs : SiteRotation240.start P =
      SiteRotation240.target P false 0 (.plain .unchanged) := rfl
  rw [startValue,hs]
  change targetValue values extra gap P false 0 .unchanged = _
  rw [target_format]
  rfl

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private theorem writeAt_set (values : List V) (r : Nat) (newValue : V) :
    writeAt values r newValue = values.set r newValue := by
  induction values generalizing r with
  | nil => rfl
  | cons first values ih => cases r <;> simp [writeAt,List.set,ih]

theorem physicalValues_write (file newValue : V) (r : Fin 9) :
    physicalValues (writeValue (r.val : V) newValue file) =
      writeAt (physicalValues file) r.val newValue := by
  rw [writeAt_set]
  apply List.ext_getElem (by simp [physicalValues_length])
  intro j hj hj'
  simp only [physicalValues,List.getElem_ofFn,reg_write,List.getElem_set,Nat.cast_inj]

theorem write_same (file : V) (r : Fin 9) :
    writeValue (r.val : V) (regValue file r) file = file :=
  ArithmeticControlTable.write_same r file

theorem effect_increment (file : V) (r : Fin 9) :
    effectValues (physicalValues file) (.increment r) =
      physicalValues (writeValue (r.val : V) (regValue file r+1) file) := by
  rw [effectValues,physicalValues_write,physicalValues_getD]

theorem effect_decrement (file : V) (r : Fin 9) :
    effectValues (physicalValues file) (.decrement r) =
      physicalValues (writeValue (r.val : V) (regValue file r-1) file) := by
  rw [effectValues,physicalValues_write,physicalValues_getD]

theorem start_source (i : Control) (file extra gap : V) :
    startValue (physicalValues file) extra gap (source i).1 =
      entryValue (number i : V) file extra gap := by
  rw [start_format]
  exact ArithmeticDispatchRebaseRotation240.start_source i file extra gap

/-- Match the whole updated file before rebasing the outgoing consumed path. -/
theorem target_entry (values : List V) (extra gap : V) (P : List Bool)
    (overflow : Bool) (padExtra : Nat) (effect : Effect) (nextFile : V)
    (hv : effectValues values effect = physicalValues nextFile)
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetValue values extra gap P overflow padExtra effect =
      entryValue (number (resolveControl P) : V) nextFile (effectExtra extra effect)
        (gap+digit overflow+(padExtra : V)) := by
  rw [target_format,box_plain,hv]
  exact ArithmeticDispatchRebaseRotation240.target_entry P overflow padExtra nextFile
    (effectExtra extra effect) gap hP hc

theorem target_next_entry (i : Control) (positive overflow : Bool) (padExtra : Nat)
    (file nextFile extra gap : V) (effect : Effect)
    (hv : effectValues (physicalValues file) effect = physicalValues nextFile)
    (hn : (source i).2 ≠ .halt)
    (hc : Clean SourceRotation240.program
      (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)) :
    targetValue (physicalValues file) extra gap
        (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)
        overflow padExtra effect =
      entryValue (nextControl i positive : V) nextFile (effectExtra extra effect)
        (gap+digit overflow+(padExtra : V)) := by
  rw [target_format,box_plain,hv]
  exact ArithmeticDispatchRebaseRotation240.target_next_entry i positive overflow
    padExtra nextFile (effectExtra extra effect) gap hn hc

end SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240
