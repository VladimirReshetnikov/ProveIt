import PA194Site48PositiveReturnCell
import PA194Site48PositiveFile
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site48PositiveReturnExact
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ReturnFileMeaning PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def returnCost (args : Fin 11 → M) : M :=
  let v := physicalArgs args
  let t1 := (1 : M)+(v 3+1)
  let t2 := (1 : M)+(v 2+1)
  let t3 := (1 : M)+(v 1+1)
  let t4 := (1 : M)+(v 0+1)
  F addCode ![modelNumeral M 1,(((t1+t2)+t3)+t4)]

theorem returnFile (args : Fin 11 → M) (base m : M) :
    let v := physicalArgs args
    let e4 : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
    let tail := F (fileCode 5) (fun i => e4 i.succ)
    let q := F ones ![m+1,tail]
    let vec : Fin 5 → M := ![v 0,v 1,v 2,v 3,(q+q)+(q+q)]
    let left := F (PA194CarryFile.leftCode 4) (Fin.cases base vec)
    let z := left+left+1
    F PA194Stepper.stepper ![returnCost args,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
      F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,F sourceFileCode (Function.update args 3 m)]] := by
  dsimp only
  let v := physicalArgs args
  let e4 : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
  let tail := F (fileCode 5) (fun i => e4 i.succ)
  let rp := F ones ![m,tail]
  let q := F ones ![m+1,tail]
  let first : Fin 4 → M := fun i => v ⟨i.val,by omega⟩
  have hq : q = rp+rp+1 := by
    dsimp only [q,rp]
    rw [show m+1 = F Code.succ (fun _ => m) from modelAddOne _,modelOnesSucc]
  let f1 := F ones ![v 3,(q+q)+(q+q)+1]
  let f2 := F ones ![v 2,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![v 1,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![v 0,(f3+f3)+(f3+f3)+1]
  have h := PA194Site48PositiveReturnCell.returnPositive first base m tail
  dsimp only at h
  change F PA194Stepper.stepper ![_,F pairCode ![modelNumeral M 4,F pairCode ![_,q]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,f4+f4]] at h
  let file0 := rp+rp+1
  let f1r := F ones ![v 3,(file0+file0)+(file0+file0)+1]
  let f2r := F ones ![v 2,(f1r+f1r)+(f1r+f1r)+1]
  let f3r := F ones ![v 1,(f2r+f2r)+(f2r+f2r)+1]
  let f4r := F ones ![v 0,(f3r+f3r)+(f3r+f3r)+1]
  have heq1 : f1r = f1 := by dsimp only [f1r,f1,file0]; rw [←hq]
  have heq2 : f2r = f2 := by dsimp only [f2r,f2]; rw [heq1]
  have heq3 : f3r = f3 := by dsimp only [f3r,f3]; rw [heq2]
  have heq4 : f4r = f4 := by dsimp only [f4r,f4]; rw [heq3]
  have hf := PA194Site48PositiveFile.returnedFile m args
  dsimp only at hf
  change F sourceFileCode (Function.update args 3 m) = f4r+f4r at hf
  rw [heq4] at hf
  rw [←hf] at h
  exact h
#print axioms returnFile
end models
end PA194Site48PositiveReturnExact
