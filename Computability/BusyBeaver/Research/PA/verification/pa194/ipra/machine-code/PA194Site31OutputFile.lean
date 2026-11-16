import PA194Site31DynamicIncrement
import PA194Site31FileCombine
import PA194RegisterPermutation
import PA194OneSpareFileRoundTrip
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31OutputFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194CarryFile PA194ReturnFile PA194ReturnFileMeaning PA194UnaryRuns PA194OneSpareReturn PA194OneSpareIdentities PA194OneSpareFileRoundTrip PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

def updated (args : Fin 11 → M) (count : M) : Fin 11 → M :=
  Function.update (Function.update args 0 (args 0+1)) 10
    (F repeatOutput ![F Code.succ (fun _ => count),(0 : M)])

theorem outputFile (args : Fin 11 → M) (count : M) :
    let v := physicalArgs args
    let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
    let marked := F (PA194MarkedFile.markedFile 3) e
    let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 3) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 6) (Fin.cases result ep)
    F sourceFileCode (updated args count) = out := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let marked := F (PA194MarkedFile.markedFile 3) e
  let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![count,six]
  let rest := F (returnCode 3) (Fin.cases tail (fun i => e i.succ))
  let result := F block ![e 0+1,rest]
  let suffix := F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]
  have htail : tail = suffix := by
    dsimp only [tail,six,suffix]
    rw [←outputBlockZero,modelOutputShift]
  have hphys : physicalArgs (updated args count) =
      Function.update (Function.update v 6 (v 6+1)) 10 suffix := by
    funext i
    fin_cases i <;> simp [updated,physicalArgs,inputOrder,v,suffix]
  rw [modelSourceFile,hphys,modelReturnMeaning,modelReturnMeaning]
  change F (fileCode 10) (Function.update (Function.update v 6 (v 6+1)) 10 suffix) =
    F (fileCode 6) (replaceLast 6 ep (F block ![e 0+1,F (fileCode 3) (replaceLast 3 (fun i => e i.succ) tail)]))
  rw [htail]
  exact PA194Site31FileCombine.combine v suffix marked
#print axioms outputFile
end models
end PA194Site31OutputFile
