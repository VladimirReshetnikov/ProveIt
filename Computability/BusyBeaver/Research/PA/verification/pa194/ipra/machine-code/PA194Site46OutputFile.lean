import PA194Site46DynamicIncrement
import PA194ReturnFileMeaning
import PA194RegisterPermutation
import PA194OneSpareFileRoundTrip
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site46OutputFile
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
  Function.update (Function.update args 3 (args 3+1)) 10
    (F repeatOutput ![F Code.succ (fun _ => count),(0 : M)])

theorem outputFile (args : Fin 11 → M) (count : M) :
    let v := physicalArgs args
    let e : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
    let marked := F (PA194MarkedFile.markedFile 5) e
    let ep : Fin 5 → M := ![v 0,v 1,v 2,v 3,marked]
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 4) (Fin.cases result ep)
    F sourceFileCode (updated args count) = out := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let e : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
  let marked := F (PA194MarkedFile.markedFile 5) e
  let ep : Fin 5 → M := ![v 0,v 1,v 2,v 3,marked]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![count,six]
  let suffix := F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]
  have htail : tail = suffix := by
    dsimp only [tail,six,suffix]
    rw [←outputBlockZero,modelOutputShift]
  have hphys : physicalArgs (updated args count) =
      Function.update (Function.update v 4 (v 4+1)) 10 suffix := by
    funext i
    fin_cases i <;> simp [updated,physicalArgs,inputOrder,v,suffix]
  have h5 : replaceLast 5 (fun i => e i.succ) suffix = ![v 5,v 6,v 7,v 8,v 9,suffix] := by
    funext i
    fin_cases i <;> rfl
  have h4 (x : M) : replaceLast 4 ep x = ![v 0,v 1,v 2,v 3,x] := by
    funext i
    fin_cases i <;> rfl
  rw [modelSourceFile,hphys,modelReturnMeaning,modelReturnMeaning]
  change F (fileCode 10) (Function.update (Function.update v 4 (v 4+1)) 10 suffix) =
    F (fileCode 4) (replaceLast 4 ep (F block ![e 0+1,F (fileCode 5) (replaceLast 5 (fun i => e i.succ) tail)]))
  rw [htail,h5,h4]
  let vv : Fin 11 → M := ![v 0,v 1,v 2,v 3,v 4+1,v 5,v 6,v 7,v 8,v 9,suffix]
  have hv : Function.update (Function.update v 4 (v 4+1)) 10 suffix = vv := by
    funext i
    fin_cases i <;> simp [vv,Function.update]
  let tt := F (fileCode 5) ![v 5,v 6,v 7,v 8,v 9,suffix]
  have htt : F (fileCode 5) (fun i => vv i.succ.succ.succ.succ.succ) = tt := by congr 1
  have ht4 : F (fileCode 6) (fun i => vv i.succ.succ.succ.succ) = F block ![v 4+1,tt] := by
    rw [modelFileSucc 5,htt]
    rfl
  have hsplit (t : M) (ht : F (fileCode 6) (fun i => vv i.succ.succ.succ.succ) = t) :
      F (fileCode 10) vv = F (fileCode 4) ![v 0,v 1,v 2,v 3,t] := by
    rw [modelFileSucc 9,modelFileSucc 8,modelFileSucc 7,modelFileSucc 6,ht]
    conv_rhs => rw [modelFileSucc 3,modelFileSucc 2,modelFileSucc 1,modelFileSucc 0,show fileCode 0 = (.proj 0 : Code 1) from rfl,modelProjection]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
    rfl
  rw [hv]
  exact hsplit _ ht4
#print axioms outputFile
end models
end PA194Site46OutputFile
