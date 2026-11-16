import ConPAMachineGenericIncrement
import PA194SpareSweep
import PA194RegisterDecrement
import PA194CompressedIncrementOracle

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

namespace PA194RegisterIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAExhaustion
open PA194ORRegisterFile PA194RegisterFile
open PA194MarkedFile PA194RegisterSplit PA194CompressedBoxFiles
open PA194CompressedBoxOracle PA194CompressedIncrementOracle
open PA194OneSpareReturn
open PA194RegisterDecrement (before marked_eq_file ordinary_eq_file)
open ConPA.Machine ConPA.Machine.Compressed

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private def after (p : Fin 9) (args : Fin 11 → M) : List M :=
  List.ofFn (fun i : Fin (8-p.val+1) => (tailArgs p args) i.castSucc)

private theorem rest_eq_file (p : Fin 9) (a : Fin 11 → M) :
    rest p a = GenericMark.file (after p a) (a 10) := by
  rw [rest,file_eq]
  congr 1
  apply congrArg a
  apply Fin.ext
  have := p.isLt
  simp
  omega

private theorem before_update (p : Fin 9) (a : Fin 11 → M) (v : M) :
    before p (Function.update a 10 v) = before p a := by
  apply congrArg List.ofFn
  funext i
  have h : (⟨i.val,by have := p.isLt; have := i.isLt; omega⟩ : Fin 11) ≠ 10 := by
    intro h
    have hi := congrArg Fin.val h
    have := p.isLt
    have := i.isLt
    simp at hi
    omega
  exact Function.update_of_ne h v a

private theorem after_update (p : Fin 9) (a : Fin 11 → M) (v : M) :
    after p (Function.update a 10 v) = after p a := by
  apply congrArg List.ofFn
  funext i
  have h : (⟨p.val+1+i.val,by have := p.isLt; have := i.isLt; omega⟩ : Fin 11) ≠ 10 := by
    intro h
    have hi := congrArg Fin.val h
    have := p.isLt
    have := i.isLt
    simp at hi
    omega
  exact Function.update_of_ne h v a

variable {T : Table} {D : GenericDecrement.Rows T}

/-- Increment with the same model-valued register file and spare-count
    convention as the folded source controller. -/
theorem incrementOracle (rows : GenericIncrement.Rows T D) (tailRows : PA194SpareSweep.Rows T D)
    (p : Fin 9) (a : Fin 11 → M) (count l : M)
    (tail : a 10 = F repeatOutput ![count,(0 : M)]) :
    Reach T (scanFrame true rows.start l (markedFileValue p a))
      (scanFrame false D.returnPositive (file (incremented a count p)) l) := by
  let newTail := F repeatOutput ![count+1,(0 : M)]
  let updated := Function.update a 10 newTail
  have output : file (incremented a count p) =
      GenericMark.file (before p a) (GenericMark.block (a (slot p)+1)
        (GenericMark.file (after p a) newTail)) := by
    change file (Function.update updated (slot p) (a (slot p)+1)) = _
    rw [ordinary_eq_file,rest_eq_file]
    exact congrArg (fun earlier => GenericMark.file earlier _) (before_update p a newTail) |>.trans
      (by simp [updated,after_update])
  have ov := GenericIncrement.increment rows (before p a) (after p a) (a (slot p)) l
    (F repeatOutput ![count,(0 : M)]) newTail (PA194SpareSweep.roundTrip tailRows count)
  simpa only [marked_eq_file,rest_eq_file,tail,output] using ov

#print axioms incrementOracle
end models
end PA194RegisterIncrement
