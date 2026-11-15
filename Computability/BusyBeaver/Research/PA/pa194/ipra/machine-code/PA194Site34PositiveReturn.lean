import PA194Site34Branch
import PA194Site32PositiveFile
import PA194Site27PositiveCell
import PA194Site27PositiveHeaderTo12
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site34PositiveReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ReturnFileMeaning PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem returnedFile (m : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let tail := F (fileCode 8) (fun i => v i.succ.succ)
    let q := F ones ![m+1,tail]
    let f := F ones ![v 0,(q+q)+(q+q)+1]
    F sourceFileCode (Function.update args 8 m) = f+f := by
  classical
  dsimp only
  let v := physicalArgs args
  let tail := F (fileCode 8) (fun i => v i.succ.succ)
  let q := F ones ![m+1,tail]
  let f := F ones ![v 0,(q+q)+(q+q)+1]
  let t := F block ![m,tail]
  have hv : physicalArgs (Function.update args 8 m) = Function.update v 1 m := by
    funext i
    fin_cases i <;> rfl
  have ht : t = q+q := by
    dsimp only [t,q]
    rw [modelBlock]
  have hf : F sourceFileCode (Function.update args 8 m) = F block ![v 0,t] := by
    rw [modelSourceFile,hv,modelFileSucc,modelFileSucc]
    rfl
  rw [hf,ht]
  exact (modelReturnBlock (v 0) (q+q)).symm

theorem positiveReturn (k : M) (args : Fin 11 → M) (m : M) (hm : args 8 = m+1) :
    let v := physicalArgs args
    let before := F ones ![k+1,modelNumeral M 800]
    let clock := F addCode ![PA194Site34Branch.clock k args,(1 : M)+(v 0+1)]
    F PA194Stepper.stepper ![clock, PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 6,F pairCode ![before+before+1,F sourceFileCode (Function.update args 8 m)]] := by
  dsimp only
  let v := physicalArgs args
  let tail := PA194Site34Branch.selectedTail args
  let q := F ones ![m+1,tail]
  let before := F ones ![k+1,modelNumeral M 800]
  have hq : q = F ones ![m,tail]+F ones ![m,tail]+1 := by
    dsimp only [q]
    rw [show m+1 = F Code.succ (fun _ => m) from modelAddOne _,modelOnesSucc]
  have h := PA194Site34Branch.positiveTo6 k args m hm
  dsimp only at h
  rw [←hq] at h
  have hmarker : PA194Site34Branch.marker k args = F ones ![v 0,(before+before+1)+(before+before+1)] + F ones ![v 0,(before+before+1)+(before+before+1)] + 1 := by
    dsimp only [PA194Site34Branch.marker]
    simp only [PA194CarryFile.modelLeftSucc, PA194CarryFile.modelLeftZero, Fin.cases_zero, Fin.cases_succ]
    rfl
  rw [hmarker] at h
  have hr := PA194Site27PositiveCell.returnCell (v 0) before q
  dsimp only at hr
  have hf := returnedFile m args
  dsimp only at hf
  change F sourceFileCode (Function.update args 8 m) = F ones ![v 0,(q+q)+(q+q)+1]+F ones ![v 0,(q+q)+(q+q)+1] at hf
  rw [←hf] at hr
  rw [PA194StepperCompose.modelStepperCompose,h]
  exact hr
theorem positiveTo12 (k : M) (args : Fin 11 → M) (m : M) (hm : args 8 = m+1) :
    let f := F sourceFileCode (Function.update args 8 m)
    let w := F ones ![k+1,(1 : M)+f+f]
    let c := F addCode ![F addCode ![PA194Site34Branch.clock k args,(1 : M)+(physicalArgs args 0+1)],
      ((1 : M)+((k+1)+1))+modelNumeral M 3]
    F PA194Stepper.stepper ![c,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 201,(w+w)+(w+w)]] := by
  dsimp only
  let updated := Function.update args 8 m
  let v := physicalArgs updated
  let f := F sourceFileCode updated
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : f = p+p := by rw [show f = F (fileCode 10) v from modelSourceFile updated,modelFileSucc,modelBlock]
  have h := positiveReturn k args m hm
  have h12 := PA194Site27PositiveHeaderTo12.headerTo12 k (modelNumeral M 100) p
  dsimp only at h12
  have n800 : ((modelNumeral M 100+modelNumeral M 100)+(modelNumeral M 100+modelNumeral M 100))+((modelNumeral M 100+modelNumeral M 100)+(modelNumeral M 100+modelNumeral M 100)) = modelNumeral M 800 := by
    repeat rw [←modelNumeralAdd]
  have n201 : modelNumeral M 100+modelNumeral M 100+1 = modelNumeral M 201 := by
    rw [←modelNumeralAdd,←modelNumeralOne,←modelNumeralAdd]
  rw [n800,n201,←hf] at h12
  have hsum : (1 : M)+f+f = (f+f)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hsum]
  rw [PA194StepperCompose.modelStepperCompose,h,h12]
#print axioms positiveTo12
#print axioms returnedFile
#print axioms positiveReturn
end models
end PA194Site34PositiveReturn
