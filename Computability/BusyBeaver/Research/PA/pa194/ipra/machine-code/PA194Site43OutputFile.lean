import PA194Site43DynamicIncrement
import PA194ReturnFileMeaning
import PA194RegisterPermutation
import PA194OneSpareFileRoundTrip
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site43OutputFile
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
  Function.update (Function.update args 8 (args 8+1)) 10
    (F repeatOutput ![F Code.succ (fun _ => count),(0 : M)])

theorem outputFile (args : Fin 11 → M) (count : M) :
    let v := physicalArgs args
    let e : Fin 10 → M := fun i => v ⟨i.val+1,by omega⟩
    let marked := F (PA194MarkedFile.markedFile 8) e
    let ep : Fin 2 → M := ![v 0,marked]
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 8) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 1) (Fin.cases result ep)
    F sourceFileCode (updated args count) = out := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let e : Fin 10 → M := fun i => v ⟨i.val+1,by omega⟩
  let marked := F (PA194MarkedFile.markedFile 8) e
  let ep : Fin 2 → M := ![v 0,marked]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![count,six]
  let suffix := F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]
  have htail : tail = suffix := by
    dsimp only [tail,six,suffix]
    rw [←outputBlockZero,modelOutputShift]
  have hphys : physicalArgs (updated args count) =
      Function.update (Function.update v 1 (v 1+1)) 10 suffix := by
    funext i
    fin_cases i <;> simp [updated,physicalArgs,inputOrder,v,suffix]
  have h8 : replaceLast 8 (fun i => e i.succ) suffix = ![v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,suffix] := by
    funext i
    fin_cases i <;> rfl
  have h1 (x : M) : replaceLast 1 ep x = ![v 0,x] := by
    funext i
    fin_cases i <;> rfl
  rw [modelSourceFile,hphys,modelReturnMeaning,modelReturnMeaning]
  change F (fileCode 10) (Function.update (Function.update v 1 (v 1+1)) 10 suffix) =
    F (fileCode 1) (replaceLast 1 ep (F block ![e 0+1,F (fileCode 8) (replaceLast 8 (fun i => e i.succ) tail)]))
  rw [htail,h8,h1]
  let vv : Fin 11 → M := ![v 0,v 1+1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,suffix]
  have hv : Function.update (Function.update v 1 (v 1+1)) 10 suffix = vv := by
    funext i
    fin_cases i <;> simp [vv,Function.update]
  let tt := F (fileCode 8) ![v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,suffix]
  have htt : F (fileCode 8) (fun i => vv i.succ.succ) = tt := by congr 1
  have ht1 : F (fileCode 9) (fun i => vv i.succ) = F block ![v 1+1,tt] := by
    rw [modelFileSucc 8,htt]
    rfl
  have hsplit (t : M) (ht : F (fileCode 9) (fun i => vv i.succ) = t) :
      F (fileCode 10) vv = F (fileCode 1) ![v 0,t] := by
    rw [modelFileSucc 9,ht]
    conv_rhs => rw [modelFileSucc 0,show fileCode 0 = (.proj 0 : Code 1) from rfl,modelProjection]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
    rfl
  rw [hv]
  exact hsplit _ ht1
#print axioms outputFile
end models
end PA194Site43OutputFile
