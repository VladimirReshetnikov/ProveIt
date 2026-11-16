import PA194Site3661ZeroRollbackCell
import PA194ReturnFileMeaning
import PA194RegisterPermutation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site3661ZeroFile
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194ReturnFile PA194ReturnFileMeaning
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def tailWord (args : Fin 11 → M) : M :=
  let v := physicalArgs args
  F ones ![v 3+1,F (fileCode 6) (fun i => v ⟨i.val+4,by omega⟩)]
noncomputable def three (args : Fin 11 → M) : Fin 4 → M :=
  let v := physicalArgs args
  let t := tailWord args
  let q := F ones ![(0 : M),t+t]
  ![v 0,v 1,0,(q+q)+(q+q)]
noncomputable def returned (args : Fin 11 → M) : M :=
  F (returnCode 3) (Fin.cases (tailWord args+tailWord args) (three args))

theorem tailIdentity (args : Fin 11 → M) :
    tailWord args+tailWord args = F (fileCode 7) (fun i : Fin 8 => physicalArgs args ⟨i.val+3,by omega⟩) := by
  unfold tailWord
  rw [modelFileSucc,modelBlock]
  have hf : (fun i : Fin 7 => physicalArgs args ⟨i.succ.val+3,by omega⟩) = (fun i : Fin 7 => physicalArgs args ⟨i.val+4,by omega⟩) := by
    funext i; congr 1
  rw [hf]
  rfl

theorem vectorIdentity (args : Fin 11 → M) (hz : args 1 = (0 : M)) :
    replaceLast 3 (three args) (tailWord args+tailWord args) =
      ![physicalArgs args 0,physicalArgs args 1,physicalArgs args 2,
        F (fileCode 7) (fun i : Fin 8 => physicalArgs args ⟨i.val+3,by omega⟩)] := by
  have hz' : physicalArgs args 2 = (0 : M) := hz
  funext i
  fin_cases i <;> first | rfl | exact hz'.symm | exact tailIdentity args

theorem splitFile (args : Fin 11 → M) :
    F (fileCode 3) ![physicalArgs args 0,physicalArgs args 1,physicalArgs args 2,
      F (fileCode 7) (fun i : Fin 8 => physicalArgs args ⟨i.val+3,by omega⟩)] = F sourceFileCode args := by
  generalize ht : F (fileCode 7) (fun i : Fin 8 => physicalArgs args ⟨i.val+3,by omega⟩) = t
  rw [modelSourceFile]
  conv_lhs => rw [modelFileSucc,modelFileSucc,modelFileSucc]
  conv_rhs => rw [modelFileSucc,modelFileSucc,modelFileSucc]
  have he : (fun i : Fin 8 => physicalArgs args i.succ.succ.succ) =
      (fun i : Fin 8 => physicalArgs args ⟨i.val+3,by omega⟩) := by
    funext i; congr 1
  rw [he,ht]
  simp only [fileCode,modelProjection]
  rfl

theorem returnedIsSourceFile (args : Fin 11 → M) (hz : args 1 = (0 : M)) :
    returned args = F sourceFileCode args := by
  rw [returned,modelReturnMeaning,vectorIdentity args hz,splitFile]
#print axioms tailIdentity
#print axioms vectorIdentity
#print axioms splitFile
#print axioms returnedIsSourceFile
end models
end PA194Site3661ZeroFile
