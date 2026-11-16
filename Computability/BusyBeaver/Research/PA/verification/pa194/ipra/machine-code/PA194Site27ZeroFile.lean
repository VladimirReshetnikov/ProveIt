import PA194Site27ZeroRollback
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroFile
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194ReturnFile PA194ReturnFileMeaning
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194Site27ZeroRollback
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem tailIdentity (e : Fin 11 → M) :
    tailWord e+tailWord e = F (fileCode 3) (fun i : Fin 4 => physicalArgs e ⟨i.val+7,by omega⟩) := by
  unfold tailWord
  rw [modelFileSucc,modelBlock]
  rfl
theorem vectorIdentity (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    replaceLast 7 (seven e) (tailWord e+tailWord e) =
      ![physicalArgs e 0,physicalArgs e 1,physicalArgs e 2,physicalArgs e 3,physicalArgs e 4,physicalArgs e 5,physicalArgs e 6,
        F (fileCode 3) (fun i : Fin 4 => physicalArgs e ⟨i.val+7,by omega⟩)] := by
  have hz' : physicalArgs e 6 = (0 : M) := by change e 0 = 0; exact hz
  funext i
  fin_cases i <;> first | rfl | exact hz'.symm | exact tailIdentity e
theorem splitFile (e : Fin 11 → M) :
    F (fileCode 7) ![physicalArgs e 0,physicalArgs e 1,physicalArgs e 2,physicalArgs e 3,physicalArgs e 4,physicalArgs e 5,physicalArgs e 6,
        F (fileCode 3) (fun i : Fin 4 => physicalArgs e ⟨i.val+7,by omega⟩)] = F sourceFileCode e := by
  generalize ht : F (fileCode 3) (fun i : Fin 4 => physicalArgs e ⟨i.val+7,by omega⟩) = t
  rw [modelSourceFile]
  conv_lhs =>
    rw [modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc]
  conv_rhs =>
    rw [modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc]
  have he : (fun i : Fin 4 => physicalArgs e i.succ.succ.succ.succ.succ.succ.succ) =
      (fun i : Fin 4 => physicalArgs e ⟨i.val+7,by omega⟩) := by
    funext i
    congr 1
  rw [he,ht]
  simp only [fileCode,modelProjection]
  rfl
theorem returnedIsSourceFile (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    returned e = F sourceFileCode e := by
  rw [returned,modelReturnMeaning,vectorIdentity e hz,splitFile]
#print axioms tailIdentity
#print axioms vectorIdentity
#print axioms splitFile
#print axioms returnedIsSourceFile
end models
end PA194Site27ZeroFile
