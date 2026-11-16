import PA194ORMark
import PA194CompressedSourceOrbit
import PA194CompressedBoxFiles

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace PA194ORRegisterFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAModelIOpenPairing PA194UnaryRuns PA194RegisterFile PA194MarkedFile
open PA194RegisterSplit PA194CompressedBoxFiles
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime (sk)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem onesDef : 𝚺₁-Function₂ (fun n t : M => F ones ![n,t]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F ones e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) ones)
  convert h using 1
  funext e
  apply congrArg (fun args : Fin 2 → M => F ones args)
  funext i
  fin_cases i <;> rfl

private theorem equalityDef (f g : M → M → M) (target : M)
    (hf : 𝚺₁-Function₂ f) (hg : 𝚺₁-Function₂ g) :
    𝚺₁-Predicate (fun n => f n target = g n target) := by
  letI := hf
  letI := hg
  definability

theorem modelOnes_eq (n tail : M) : F ones ![n,tail] = bitPrefix true n tail := by
  let g (n t : M) := F ones ![n,t]
  have rightDef : 𝚺₁-Function₂ (bitPrefix (V := M) true) := by
    change 𝚺₁-Function₂ (SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix (V := M))
    definability
  change g n tail = bitPrefix true n tail
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact equalityDef g (bitPrefix true) tail onesDef rightDef
  | zero =>
    change F ones ![(0 : M),tail] = _
    rw [modelOnesZero,bitPrefix_zero]
  | succ n ih =>
    change F ones ![n,tail] = _ at ih
    change F ones ![F addCode ![n,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc,ih,bitPrefix_succ]
    simp only [two_mul, Bool.toNat_true, Nat.cast_one]

theorem block_eq (n tail : M) : F block ![n,tail] = PA194ORMark.block n tail := by
  rw [modelBlock,modelOnes_eq,PA194ORMark.block,push]
  simp only [Bool.toNat_false,Nat.cast_zero,add_zero,two_mul]

theorem marked_eq (n tail : M) : F markedBlock ![n,tail] = PA194ORMark.marked n tail := by
  rw [modelMarkedBlock,modelOnes_eq,PA194ORMark.marked]
  simp only [push,Bool.toNat_false,Nat.cast_zero,add_zero,two_mul]

theorem file_eq (n : Nat) (args : Fin (n+1) → M) :
    F (fileCode n) args =
      PA194ORMark.file (List.ofFn (fun i : Fin n => args i.castSucc)) (args (Fin.last n)) := by
  induction n with
  | zero => rw [fileCode,modelProjection]; rfl
  | succ n ih =>
    rw [modelFileSucc,block_eq,ih,List.ofFn_succ]
    rfl

theorem markEntry (p : Fin 9) :
    PA194ORMark.control p.val = PA194ORData.denseControl (sk p.val) := by
  fin_cases p <;> decide +kernel

theorem markExit (p : Fin 9) :
    PA194ORMark.returnControl p.val = PA194ORData.denseControl (M6.Runtime.markExit p.val) := by
  fin_cases p <;> decide +kernel

/-- The exact OR literal marking routine realizes the register-file marking
    used by the controller in any PRA expansion of an IΣ₁ model. -/
theorem markOracle (p : Fin 9) (args : Fin 11 → M) (left : M) :
    Reach PA194ORData.table (scanFrame true (PA194ORData.denseControl (sk p.val)) left (file args))
      (scanFrame false (PA194ORData.denseControl (M6.Runtime.markExit p.val)) (markedFileValue p args) left) := by
  let earlier := List.ofFn (fun i : Fin p.val => (frontArgs p args (0 : M)) i.castSucc)
  have common (value : M) : F (fileCode p.val) (frontArgs p args value) =
      PA194ORMark.file earlier value := by
    rw [file_eq,frontLast]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp [frontArgs]
  have input : file args = PA194ORMark.file earlier (PA194ORMark.block (args (slot p)) (rest p args)) := by
    rw [← ordinaryFileSplit_self p args, common, block_eq]
  have output : markedFileValue p args =
      PA194ORMark.file earlier (PA194ORMark.marked (args (slot p)) (rest p args)) := by
    rw [markedFileValue,common,marked,marked_eq]
  have length : earlier.length = p.val := List.length_ofFn
  have result := PA194ORMark.mark earlier (by rw [length]; exact p.isLt)
    (args (slot p)) left (rest p args)
  rw [length,markEntry p,markExit p,← input,← output] at result
  exact reachable result

#print axioms modelOnes_eq
#print axioms file_eq
#print axioms markOracle
end models
end PA194ORRegisterFile
