import PA194Site32ZeroRollbackCell
import PA194ReturnFileMeaning
import PA194RegisterPermutation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroFile
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
  F ones ![v 9+1,v 10]
noncomputable def nine (args : Fin 11 → M) : Fin 10 → M :=
  let v := physicalArgs args
  let t := tailWord args
  let q := F ones ![(0 : M),t+t]
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,0,(q+q)+(q+q)]
noncomputable def returned (args : Fin 11 → M) : M :=
  F (returnCode 9) (Fin.cases (tailWord args+tailWord args) (nine args))

theorem tailIdentity (args : Fin 11 → M) :
    tailWord args+tailWord args = F (fileCode 1) (fun i : Fin 2 => physicalArgs args ⟨i.val+9,by omega⟩) := by
  unfold tailWord
  rw [modelFileSucc,modelBlock]
  have hf : (fun i : Fin 1 => physicalArgs args ⟨i.succ.val+9,by omega⟩) = ![physicalArgs args 10] := by
    funext i; fin_cases i <;> rfl
  rw [hf,modelFileZero]
  rfl

theorem vectorIdentity (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    replaceLast 9 (nine args) (tailWord args+tailWord args) =
      ![physicalArgs args 0,physicalArgs args 1,physicalArgs args 2,physicalArgs args 3,physicalArgs args 4,physicalArgs args 5,physicalArgs args 6,physicalArgs args 7,physicalArgs args 8,
        F (fileCode 1) (fun i : Fin 2 => physicalArgs args ⟨i.val+9,by omega⟩)] := by
  have hz' : physicalArgs args 8 = (0 : M) := hz
  funext i
  fin_cases i <;> first | rfl | exact hz'.symm | exact tailIdentity args

theorem splitFile (args : Fin 11 → M) :
    F (fileCode 9) ![physicalArgs args 0,physicalArgs args 1,physicalArgs args 2,physicalArgs args 3,physicalArgs args 4,physicalArgs args 5,physicalArgs args 6,physicalArgs args 7,physicalArgs args 8,
      F (fileCode 1) (fun i : Fin 2 => physicalArgs args ⟨i.val+9,by omega⟩)] = F sourceFileCode args := by
  generalize ht : F (fileCode 1) (fun i : Fin 2 => physicalArgs args ⟨i.val+9,by omega⟩) = t
  rw [modelSourceFile]
  conv_lhs => rw [modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc]
  conv_rhs => rw [modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc]
  have he : (fun i : Fin 2 => physicalArgs args i.succ.succ.succ.succ.succ.succ.succ.succ.succ) =
      (fun i : Fin 2 => physicalArgs args ⟨i.val+9,by omega⟩) := by
    funext i; congr 1
  rw [he,ht]
  simp only [fileCode,modelProjection]
  rfl

theorem returnedIsSourceFile (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    returned args = F sourceFileCode args := by
  rw [returned,modelReturnMeaning,vectorIdentity args hz,splitFile]
#print axioms tailIdentity
#print axioms vectorIdentity
#print axioms splitFile
#print axioms returnedIsSourceFile
end models
end PA194Site32ZeroFile
