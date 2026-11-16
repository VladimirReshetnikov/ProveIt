import Mathlib.Tactic.FinCases
import PA194RegisterPermutation
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PositiveOutputFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194OnesCommute PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem sourceFileAfterDecrement (m : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let v1 : Fin 10 → M := fun i => v i.succ
    let rem : Fin 9 → M := fun i => v1 i.succ
    let rp := F ones ![m,F (fileCode 8) rem]
    let tp := rp+rp+1
    let rf := tp+tp
    let file := rf+rf+1
    let final := F ones ![v 0,file]
    let updated := Function.update args 8 m
    let f := F sourceFileCode updated
    (1 : M)+(final+final)+(final+final) = (1 : M)+(f+f) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let v1 : Fin 10 → M := fun i => v i.succ
  let rem : Fin 9 → M := fun i => v1 i.succ
  let rp := F ones ![m,F (fileCode 8) rem]
  let tp := rp+rp+1
  let rf := tp+tp
  let file := rf+rf+1
  let final := F ones ![v 0,file]
  let updated := Function.update args 8 m
  let f := F sourceFileCode updated
  let tail := (rp+rp+1)+(rp+rp+1)
  let out := F ones ![v 0,tail]
  have hv : physicalArgs updated = Fin.cases (v 0) (Fin.cases m rem) := by
    funext i
    fin_cases i <;> rfl
  have htail : F (fileCode 9) (Fin.cases m rem) = tail := by
    rw [modelFileSucc,modelBlock]
    simp only [Fin.cases_zero,Fin.cases_succ]
    change F ones ![F addCode ![m,F oneCode Fin.elim0],F (fileCode 8) rem] +
      F ones ![F addCode ![m,F oneCode Fin.elim0],F (fileCode 8) rem] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : f = ((out+out)+(out+out))+1+1 := by
    dsimp only [f]
    rw [modelSourceFile,hv,modelFileSucc,modelBlock]
    simp only [Fin.cases_zero,Fin.cases_succ]
    rw [htail]
    change F ones ![F addCode ![v 0,F oneCode Fin.elim0],tail] +
      F ones ![F addCode ![v 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
    change (out+out+1)+(out+out+1) = ((out+out)+(out+out))+1+1
    simp only [add_assoc,add_comm,add_left_comm]
  have hfinal : final = out+out+1 := by
    dsimp only [final,out]
    have h := modelOnesCommute (v 0) tail
    have hfile : file = tail+tail+1 := by rfl
    rw [hfile]
    exact h
  change (1 : M)+(final+final)+(final+final) = (1 : M)+(f+f)
  rw [hfinal,hf]
  change (1 : M)+((out+out+1)+(out+out+1))+((out+out+1)+(out+out+1)) =
    (1 : M)+((((out+out)+(out+out))+1+1)+(((out+out)+(out+out))+1+1))
  simp only [add_assoc,add_comm,add_left_comm]
#print axioms sourceFileAfterDecrement
end models
end PA194PositiveOutputFile
