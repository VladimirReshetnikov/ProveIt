import PA194Site34Branch
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34ZeroFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning BinaryTapeCodes TableDispatch PA194UnaryRuns PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def tailWord (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  F ones ![e 2+1,F (fileCode 7) (fun i => e i.succ.succ.succ)]
noncomputable def vec (args : Fin 11 → M) : Fin 3 → M :=
  let e := physicalArgs args
  let t := tailWord args
  let q := F ones ![(0 : M),t+t]
  ![e 0,0,(q+q)+(q+q)]
noncomputable def returned (args : Fin 11 → M) : M :=
  let t := tailWord args
  F (returnCode 2) (Fin.cases (t+t) (vec args))

theorem tailIdentity (args : Fin 11 → M) :
    tailWord args+tailWord args = F (fileCode 8) (fun i => physicalArgs args i.succ.succ) := by
  unfold tailWord
  rw [modelFileSucc,modelBlock]
  rfl

theorem vectorIdentity (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    replaceLast 2 (vec args) (tailWord args+tailWord args) =
      ![physicalArgs args 0,physicalArgs args 1,F (fileCode 8) (fun i => physicalArgs args i.succ.succ)] := by
  have hz' : physicalArgs args 1 = (0 : M) := hz
  funext i
  fin_cases i <;> first | rfl | exact hz'.symm | exact tailIdentity args

theorem splitFile (args : Fin 11 → M) :
    F (fileCode 2) ![physicalArgs args 0,physicalArgs args 1,F (fileCode 8) (fun i => physicalArgs args i.succ.succ)] =
      F sourceFileCode args := by
  generalize ht : F (fileCode 8) (fun i => physicalArgs args i.succ.succ) = t
  rw [modelSourceFile]
  conv_lhs => rw [modelFileSucc,modelFileSucc]
  conv_rhs => rw [modelFileSucc,modelFileSucc]
  rw [ht]
  simp only [fileCode,modelProjection]
  rfl

theorem returnedIsSourceFile (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    returned args = F sourceFileCode args := by
  rw [returned,modelReturnMeaning,vectorIdentity args hz,splitFile]
#print axioms tailIdentity
#print axioms vectorIdentity
#print axioms splitFile
#print axioms returnedIsSourceFile
end models
end PA194Site34ZeroFile
