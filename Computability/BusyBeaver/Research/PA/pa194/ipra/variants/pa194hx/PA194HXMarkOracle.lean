import PA194HXGenericMark
import PA194HXRowData
import PA194HXAllocation
import PA194ORRegisterFile
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194HXMarkOracle
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAModelIOpenPairing PA194UnaryRuns PA194RegisterFile PA194MarkedFile
open PA194RegisterSplit PA194CompressedBoxFiles
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime (sk)

theorem markEntry (p : Fin 9) :
    PA194HXGenericMark.control p.val = PA194HXRowData.denseControl (sk p.val) := by
  fin_cases p <;> decide +kernel

theorem markExit (p : Fin 9) :
    (if p.val = 0 then 15 else 17) =
      PA194HXRowData.denseControl (M6.Runtime.markExit p.val) := by
  fin_cases p <;> decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The model-length physical HX mark routine implements every M6 mark
    oracle call, with arbitrary model-valued physical register contents. -/
theorem markOracle (p : Fin 9) (args : Fin 11 → M) (left : M) :
    Reach PA194HXDispatch.table (scanFrame true (PA194HXRowData.denseControl (sk p.val)) left (file args))
      (scanFrame false (PA194HXRowData.denseControl (M6.Runtime.markExit p.val)) (markedFileValue p args) left) := by
  let earlier := List.ofFn (fun i : Fin p.val => (frontArgs p args (0 : M)) i.castSucc)
  have common (value : M) : F (fileCode p.val) (frontArgs p args value) =
      PA194ORMark.file earlier value := by
    rw [PA194ORRegisterFile.file_eq,frontLast]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp [frontArgs]
  have input : file args = PA194ORMark.file earlier (PA194ORMark.block (args (slot p)) (rest p args)) := by
    rw [← ordinaryFileSplit_self p args, common, PA194ORRegisterFile.block_eq]
  have output : markedFileValue p args =
      PA194ORMark.file earlier (PA194ORMark.marked (args (slot p)) (rest p args)) := by
    rw [markedFileValue,common,marked,PA194ORRegisterFile.marked_eq]
  have length : earlier.length = p.val := List.length_ofFn
  have result := PA194HXGenericMark.mark earlier (by rw [length]; exact p.isLt)
    (args (slot p)) left (rest p args)
  rw [length,markEntry p,markExit p,← input,← output] at result
  exact reachable result

/-- The same oracle instantiated at the HX physical location of any logical
    source register, including the exchanged H and X fields. -/
theorem logicalMarkOracle (r : Fin 9) (args : Fin 11 → M) (left : M) :
    Reach PA194HXDispatch.table
      (scanFrame true (PA194HXRowData.denseControl (sk (PA194HXAllocation.hx r).val)) left
        (F PA194HXAllocation.sourceFileCode args))
      (scanFrame false (PA194HXRowData.denseControl (M6.Runtime.markExit (PA194HXAllocation.hx r).val))
        (markedFileValue (PA194HXAllocation.hx r) (PA194HXAllocation.physicalArgs args)) left) := by
  rw [PA194HXAllocation.modelSourceFile]
  exact markOracle (PA194HXAllocation.hx r) (PA194HXAllocation.physicalArgs args) left

#print axioms markEntry
#print axioms markExit
#print axioms markOracle
#print axioms logicalMarkOracle
end models
end PA194HXMarkOracle
