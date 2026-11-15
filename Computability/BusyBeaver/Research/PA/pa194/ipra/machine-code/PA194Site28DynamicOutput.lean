import PA194OneSpareReturn
import PA194Site28FinishReturn
import PA194Site28SeedOutput
import PA194ReturnFileMeaning
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28DynamicOutput
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28FinishReturn PA194Site28SeedOutput PA194RegisterPermutation PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning PA194UnaryRuns PA194OneSpareReturn PA194OnesCommute PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnAppendBlock (n : Nat) (e : Fin (n+2) → M) :
    let vals : Fin (n+1) → M := fun i => e i.castSucc
    F (returnCode n) (Fin.cases (F block ![e ⟨n,by omega⟩,e (Fin.last (n+1))]) vals) =
      F (fileCode (n+1)) e := by
  induction n with
  | zero =>
    dsimp only
    rw [modelReturnCodeZero,modelFileSucc]
    change F block ![e 0,e 1] = F block ![e 0,F (.proj 0) (fun i => e i.succ)]
    rw [modelProjection]
    rfl
  | succ n ih =>
    let vals : Fin (n+2) → M := fun i => e i.castSucc
    let e1 : Fin (n+2) → M := fun i => e i.succ
    let t := F block ![e ⟨n+1,by omega⟩,e (Fin.last (n+2))]
    have h := modelReturnCodeSucc (M := M) n (Fin.cases t vals)
    dsimp only at h
    have hi := ih e1
    dsimp only at hi
    rw [modelFileSucc] 
    change F (returnCode (n+1)) (Fin.cases t vals) = F block ![e 0,F (fileCode (n+1)) e1]
    rw [h,modelReturnBlock]
    simp only [Fin.cases_zero,Fin.cases_succ]
    congr 1
    funext i
    fin_cases i
    · rfl
    · change F (returnCode n) (Fin.cases t (fun i => e1 i.castSucc)) = F (fileCode (n+1)) e1
      exact hi
def updated (args : Fin 11 → M) (count : M) : Fin 11 → M :=
  Function.update (Function.update args 8 (args 8+1)) 10
    (F repeatOutput ![F Code.succ (fun _ => count),(0 : M)])

theorem outputFile (args : Fin 11 → M) (count : M) :
    let tail := F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]
    let es := PA194Site28FinishReturn.rest args
    let vals : Fin 8 → M := fun i => es i.castSucc
    let seedOut := F block ![args 9,tail]
    let out := F (returnCode 7) (Fin.cases seedOut vals)
    let w1 := F ones ![args 8+1,(1 : M)+out+out]
    let p := F ones ![args 2,(1 : M)+(w1+w1)+(w1+w1)]
    F sourceFileCode (updated args count) = p+p := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let tail := F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]
  let es := PA194Site28FinishReturn.rest args
  let vals : Fin 8 → M := fun i => es i.castSucc
  let seedOut := F block ![args 9,tail]
  let out := F (returnCode 7) (Fin.cases seedOut vals)
  let w1 := F ones ![args 8+1,(1 : M)+out+out]
  let p := F ones ![args 2,(1 : M)+(w1+w1)+(w1+w1)]
  let sf : Fin 9 → M := Fin.snoc vals tail
  have hsf : (fun i : Fin 8 => sf i.castSucc) = vals := by
    funext i
    simp only [sf,Fin.snoc_castSucc]
  have hlast : sf ⟨7,by decide⟩ = args 9 := by rfl
  have htail : sf (Fin.last 8) = tail := by simp only [sf,Fin.snoc_last]
  have happ := returnAppendBlock (M := M) 7 sf
  dsimp only at happ
  change F (returnCode 7) (Fin.cases (F block ![sf ⟨7,by decide⟩,sf (Fin.last 8)])
    (fun i : Fin 8 => sf i.castSucc)) = F (fileCode 8) sf at happ
  rw [hsf,hlast,htail] at happ
  have hout : out = F (fileCode 8) sf := happ
  let changed := updated args count
  let physical := physicalArgs changed
  have h0 : physical 0 = args 2 := by simp [physical,changed,updated,physicalArgs,inputOrder]
  have h1 : physical 1 = args 8+1 := by simp [physical,changed,updated,physicalArgs,inputOrder]
  have hrest : (fun i : Fin 9 => physical i.succ.succ) = sf := by
    funext i
    fin_cases i <;> simp [physical,changed,updated,physicalArgs,inputOrder,sf,es,rest,Fin.snoc,vals,tail]
  have hfile : F sourceFileCode changed = F block ![args 2,F block ![args 8+1,out]] := by
    rw [modelSourceFile,modelFileSucc,modelFileSucc]
    change F block ![physical 0,F block ![physical 1,F (fileCode 8) (fun i => physical i.succ.succ)]] = _
    rw [h0,h1,hrest,←hout]
  have hw1 : F block ![args 8+1,out] = w1+w1 := by
    rw [←modelReturnBlock]
    have harg : out+out+1 = (1 : M)+out+out := by simp only [add_assoc,add_comm,add_left_comm]
    rw [harg]
  have hp : F block ![args 2,w1+w1] = p+p := by
    rw [←modelReturnBlock]
    have harg : (w1+w1)+(w1+w1)+1 = (1 : M)+(w1+w1)+(w1+w1) := by simp only [add_assoc,add_comm,add_left_comm]
    rw [harg]
  change F sourceFileCode changed = p+p
  rw [hfile,hw1,hp]
#print axioms outputFile
#print axioms returnAppendBlock
end models
end PA194Site28DynamicOutput
