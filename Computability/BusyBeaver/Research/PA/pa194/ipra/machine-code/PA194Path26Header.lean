import PA194Path27Header
import PA194PositiveOutputFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path26Header
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PA194PositiveOutputFile PA194Path27Header PRAModelIOpenPairing TableDispatch

theorem path26 : PA194SourceProgram.path 26 = [true,false,false,false,false,true] := by
  decide +kernel
#print axioms path26
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem path26Word (z : M) :
    let r := (z+z)+(z+z)
    let t := (1 : M)+r+r
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let t5 := t4+t4
    modelWord (PA194SourceProgram.path 26) ((z+z)+(z+z)) = t5+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [path26]
  simp only [modelWord, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  simp only [add_assoc,add_comm,add_left_comm]

theorem positiveResultIsPath26 (k m : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let v1 : Fin 10 → M := fun i => v i.succ
    let rem : Fin 9 → M := fun i => v1 i.succ
    let rp := F ones ![m,F (fileCode 8) rem]
    let tp := rp+rp+1
    let rf := tp+tp
    let file := rf+rf+1
    let final := F ones ![v 0,file]
    let z := F zeros ![k+1,(1 : M)+(final+final)+(final+final)]
    let rr := (z+z)+(z+z)
    let t := (1 : M)+rr+rr
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let t5 := t4+t4
    let f := F sourceFileCode (Function.update args 8 m)
    t5+1 = modelWord (PA194SourceProgram.path 26)
      (F zeros ![((k+1)+1)+1,(1 : M)+(f+f)]) := by
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
  let f := F sourceFileCode (Function.update args 8 m)
  let z := F zeros ![k+1,(1 : M)+(final+final)+(final+final)]
  let rr := (z+z)+(z+z)
  let t := (1 : M)+rr+rr
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  let t5 := t4+t4
  change t5+1 = modelWord (PA194SourceProgram.path 26) (F zeros ![((k+1)+1)+1,(1 : M)+(f+f)])
  have hf : (1 : M)+(final+final)+(final+final) = (1 : M)+(f+f) := by
    have h := sourceFileAfterDecrement m args
    dsimp only at h
    exact h
  have hz : F zeros ![((k+1)+1)+1,(1 : M)+(f+f)] = (z+z)+(z+z) := by
    rw [show ((k+1)+1)+1 = F Code.succ (fun _ => (k+1)+1) from modelAddOne _,modelZerosSucc,
      show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelZerosSucc]
    rw [←hf]
  rw [hz]
  exact (path26Word z).symm
#print axioms path26Word
#print axioms positiveResultIsPath26
end models
end PA194Path26Header
