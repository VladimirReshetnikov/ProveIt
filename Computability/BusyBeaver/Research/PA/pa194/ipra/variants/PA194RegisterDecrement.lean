import ConPAMachineGenericDecrement
import PA194ORRegisterFile
import PA194CompressedBoxOracle

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

namespace PA194RegisterDecrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAExhaustion
open PA194ORRegisterFile PA194RegisterFile
open PA194MarkedFile PA194RegisterSplit PA194CompressedBoxFiles
open PA194CompressedBoxOracle
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

def before (p : Fin 9) (args : Fin 11 → M) : List M :=
  List.ofFn (fun i : Fin p.val => args ⟨i.val,by have := p.isLt; have := i.isLt; omega⟩)

private theorem front_eq (p : Fin 9) (a : Fin 11 → M) (value : M) :
    F (fileCode p.val) (frontArgs p a value) = ConPA.Machine.GenericMark.file (before p a) value := by
  rw [file_eq,frontLast]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [frontArgs]

theorem marked_eq_file (p : Fin 9) (a : Fin 11 → M) :
    markedFileValue p a =
      ConPA.Machine.GenericMark.file (before p a) (ConPA.Machine.GenericMark.marked (a (slot p)) (rest p a)) := by
  rw [markedFileValue,front_eq,marked,marked_eq]
  rfl

theorem ordinary_eq_file (p : Fin 9) (a : Fin 11 → M) (v : M) :
    file (Function.update a (slot p) v) =
      ConPA.Machine.GenericMark.file (before p a) (ConPA.Machine.GenericMark.block v (rest p a)) := by
  rw [← ordinaryFileSplit,front_eq,block_eq]
  rfl

variable {T : Table} (rows : GenericDecrement.Rows T)

theorem zeroOracle (p : Fin 9) (a : Fin 11 → M) (l : M) (zero : a (slot p) = 0) :
    Reach T (scanFrame true rows.scanRight l (markedFileValue p a))
      (scanFrame false rows.returnZero (file a) l) := by
  have ordinary : file a = ConPA.Machine.GenericMark.file (before p a) (ConPA.Machine.GenericMark.block 0 (rest p a)) := by
    rw [← ordinaryFileSplit_self p a,front_eq,block_eq,zero]
    rfl
  have restBlock : rest p a = ConPA.Machine.GenericMark.block (tailArgs p a 0)
      (F (fileCode (8-p.val)) (fun i => tailArgs p a i.succ)) := by
    rw [rest,modelFileSucc,block_eq]
    rfl
  have ov := GenericDecrement.zero rows (before p a) l (tailArgs p a 0)
    (F (fileCode (8-p.val)) (fun i => tailArgs p a i.succ))
  simpa only [marked_eq_file,zero,ordinary,restBlock] using ov

theorem positiveOracle (p : Fin 9) (a : Fin 11 → M) (l : M) (positive : a (slot p) ≠ 0) :
    Reach T (scanFrame true rows.scanRight l (markedFileValue p a))
      (scanFrame false rows.returnPositive (file (decrement a p)) (push true l)) := by
  let d := F predCode (fun _ => a (slot p))
  have count : a (slot p) = d+1 := by
    have h := (modelZeroOrSuccPred (a (slot p))).resolve_left positive
    change a (slot p) = F addCode ![d,F oneCode Fin.elim0]
    rw [modelAddOne]
    exact h.symm
  have post : file (decrement a p) =
      ConPA.Machine.GenericMark.file (before p a) (ConPA.Machine.GenericMark.block d (rest p a)) := ordinary_eq_file p a d
  rw [post,marked_eq_file,count]
  exact GenericDecrement.positive rows (before p a) d l (rest p a)

#print axioms zeroOracle
#print axioms positiveOracle
end models
end PA194RegisterDecrement
