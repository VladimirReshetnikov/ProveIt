import PA194CompressedBoxOracle
import PA194RepeatedSpareFileIncrement

set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194CompressedIncrementOracle
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194IncrementFront PA194ReturnFile PA194ReturnFileMeaning PA194ReturnCell PA194OnesCommute
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

open PA194CompressedBoxFiles PA194CompressedBoxOracle PA194FoldedRuntimeRows

noncomputable def incremented (a : Fin 11 → M) (count : M) (p : Fin 9) : Fin 11 → M :=
  Function.update (Function.update a 10 (F repeatOutput ![count+1,(0 : M)])) (slot p) (a (slot p)+1)

/-- The increment branch of the compressed register oracle with one new trailing spare. -/
theorem incrementOracle (a : Fin 11 → M) (count : M)
    (h : a 10 = F repeatOutput ![count,(0 : M)]) : IncrementOracle a (incremented a count) := by
  intro p l
  rw [show denseControl 64 = 2 by decide +kernel, show denseControl 40 = 7 by decide +kernel]
  exact PA194RepeatedSpareFileIncrement.incrementOracle p a count l h

/-- The complete model-local oracle with a repeated-spare suffix. -/
theorem concreteBoxAgreement (a : Fin 11 → M) (count : M) (br : M6.Runtime.Branch)
    (h : a 10 = F repeatOutput ![count,(0 : M)]) (hb : BranchOK a br) :
    PA194CompressedExecutor.BoxAgreement denseControl br (boxValue a (incremented a count)) :=
  boxAgreement a _ (incrementOracle a count h) br hb

#print axioms incrementOracle
#print axioms concreteBoxAgreement
end models
end PA194CompressedIncrementOracle
