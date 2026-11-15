import PA194Site38PositiveReturnCell
import PA194Site38PositiveFile
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site38PositiveReturnExact
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
  let t1 := (1 : M)+(v 4+1)
  let t2 := (1 : M)+(v 3+1)
  let t3 := (1 : M)+(v 2+1)
  let t4 := (1 : M)+(v 1+1)
  let t5 := (1 : M)+(v 0+1)
  F addCode ![modelNumeral M 1,((((t1+t2)+t3)+t4)+t5)]

theorem returnFile (args : Fin 11 → M) (base m : M) :
    let v := physicalArgs args
    let e5 : Fin 6 → M := fun i => v ⟨i.val+5,by omega⟩
    let tail := F (fileCode 4) (fun i => e5 i.succ)
    let q := F ones ![m+1,tail]
    let vec : Fin 6 → M := ![v 0,v 1,v 2,v 3,v 4,(q+q)+(q+q)]
    let left := F (PA194CarryFile.leftCode 5) (Fin.cases base vec)
    let z := left+left+1
    F PA194Stepper.stepper ![returnCost args,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
      F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,F sourceFileCode (Function.update args 7 m)]] := by
  dsimp only
  let v := physicalArgs args
  let e5 : Fin 6 → M := fun i => v ⟨i.val+5,by omega⟩
  let tail := F (fileCode 4) (fun i => e5 i.succ)
  let rp := F ones ![m,tail]
  let q := F ones ![m+1,tail]
  let first : Fin 5 → M := fun i => v ⟨i.val,by omega⟩
  have hq : q = rp+rp+1 := by
    dsimp only [q,rp]
    rw [show m+1 = F Code.succ (fun _ => m) from modelAddOne _,modelOnesSucc]
  let f1 := F ones ![v 4,(q+q)+(q+q)+1]
  let f2 := F ones ![v 3,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![v 2,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![v 1,(f3+f3)+(f3+f3)+1]
  let f5 := F ones ![v 0,(f4+f4)+(f4+f4)+1]
  have h := PA194Site38PositiveReturnCell.returnPositive first base m tail
  dsimp only at h
  change F PA194Stepper.stepper ![_,F pairCode ![modelNumeral M 4,F pairCode ![_,q]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,f5+f5]] at h
  let file0 := rp+rp+1
  let f1r := F ones ![v 4,(file0+file0)+(file0+file0)+1]
  let f2r := F ones ![v 3,(f1r+f1r)+(f1r+f1r)+1]
  let f3r := F ones ![v 2,(f2r+f2r)+(f2r+f2r)+1]
  let f4r := F ones ![v 1,(f3r+f3r)+(f3r+f3r)+1]
  let f5r := F ones ![v 0,(f4r+f4r)+(f4r+f4r)+1]
  have heq1 : f1r = f1 := by dsimp only [f1r,f1,file0]; rw [←hq]
  have heq2 : f2r = f2 := by dsimp only [f2r,f2]; rw [heq1]
  have heq3 : f3r = f3 := by dsimp only [f3r,f3]; rw [heq2]
  have heq4 : f4r = f4 := by dsimp only [f4r,f4]; rw [heq3]
  have heq5 : f5r = f5 := by dsimp only [f5r,f5]; rw [heq4]
  have hf := PA194Site38PositiveFile.returnedFile m args
  dsimp only at hf
  change F sourceFileCode (Function.update args 7 m) = f5r+f5r at hf
  rw [heq5] at hf
  rw [←hf] at h
  exact h
#print axioms returnFile
end models
end PA194Site38PositiveReturnExact
