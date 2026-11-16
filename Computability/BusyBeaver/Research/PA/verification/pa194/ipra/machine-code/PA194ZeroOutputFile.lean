import PA194RegisterPermutation
import PA194UnaryRuns
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroOutputFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem sourceFileAfterZero (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    let v := physicalArgs args
    let v1 : Fin 10 → M := fun i => v i.succ
    let rem : Fin 9 → M := fun i => v1 i.succ
    let r := F ones ![rem 0,F (fileCode 7) (fun i => rem i.succ)]
    let p := r+r+1
    let u := p+p
    let file := (u+u+1)+(u+u+1)
    let out := F ones ![v 0,file]
    F sourceFileCode args = ((out+out)+(out+out))+1+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let v1 : Fin 10 → M := fun i => v i.succ
  let rem : Fin 9 → M := fun i => v1 i.succ
  let tail := F (fileCode 7) (fun i => rem i.succ)
  let r := F ones ![rem 0,tail]
  let p := r+r+1
  let u := p+p
  let file := (u+u+1)+(u+u+1)
  let out := F ones ![v 0,file]
  change F sourceFileCode args = ((out+out)+(out+out))+1+1
  have hz' : v1 0 = (0 : M) := by exact hz
  have h8 : F (fileCode 8) rem = p+p := by
    rw [modelFileSucc,modelBlock]
    change F ones ![F addCode ![rem 0,F oneCode Fin.elim0],tail] + F ones ![F addCode ![rem 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have h9 : F (fileCode 9) v1 = file := by
    rw [modelFileSucc,modelBlock,hz']
    simp only [zero_add]
    have hs : (1 : M) = F Code.succ (fun _ => (0 : M)) := by
      have h := modelAddOne (0 : M)
      change (0 : M)+1 = _ at h
      simpa only [zero_add] using h
    rw [hs,modelOnesSucc,modelOnesZero,h8]
  rw [modelSourceFile,modelFileSucc,modelBlock]
  change F ones ![F addCode ![v 0,F oneCode Fin.elim0],F (fileCode 9) v1] +
    F ones ![F addCode ![v 0,F oneCode Fin.elim0],F (fileCode 9) v1] = _
  rw [modelAddOne,modelOnesSucc,h9]
  dsimp only [out]
  simp only [add_assoc,add_comm,add_left_comm]
#print axioms sourceFileAfterZero
end models
end PA194ZeroOutputFile
