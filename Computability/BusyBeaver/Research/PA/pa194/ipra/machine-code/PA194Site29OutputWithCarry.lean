import PA194Site29SeedOutput
import PA194Site28OutputFile
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29OutputWithCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning PA194UnaryRuns PA194StateOne PA194FiniteControls PA194StartupSourceFrame PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def updated (args : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update args 6 (args 6+1)) 10
    (F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]])
theorem blockAsOnes (n t : M) : F block ![n,t] =
    F ones ![n,(1 : M)+t+t]+F ones ![n,(1 : M)+t+t] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [←modelReturnBlock]
  have h : t+t+1 = (1 : M)+t+t := by simp only [add_assoc,add_comm,add_left_comm]
  rw [h]

def fileHalf : (n : Nat) → (Fin (n+2) → M) → M
  | 0, e => F ones ![e 0,(1 : M)+e 1+e 1]
  | n+1, e =>
    let h := fileHalf n (fun i => e i.succ)
    F ones ![e 0,(1 : M)+(h+h)+(h+h)]
theorem fileHalfCorrect (n : Nat) (e : Fin (n+2) → M) :
    F (fileCode (n+1)) e = fileHalf n e+fileHalf n e := by
  induction n with
  | zero =>
    rw [modelFileSucc]
    change F block ![e 0,F (.proj 0) (fun i => e i.succ)] = _
    rw [modelProjection]
    exact blockAsOnes (e 0) (e 1)
  | succ n ih =>
    rw [modelFileSucc,ih,blockAsOnes]
    rfl

theorem outputFile (args : Fin 11 → M) :
    let v := physicalArgs args
    let suffix := F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]]
    let tail := F block ![v 9,suffix]
    let r0 := F ones ![v 8+1,(1 : M)+tail+tail]
    let r1 := F ones ![v 7,(1 : M)+(r0+r0)+(r0+r0)]
    let r2 := F ones ![v 6,(1 : M)+(r1+r1)+(r1+r1)]
    let r3 := F ones ![v 5,(1 : M)+(r2+r2)+(r2+r2)]
    let r4 := F ones ![v 4,(1 : M)+(r3+r3)+(r3+r3)]
    let r5 := F ones ![v 3,(1 : M)+(r4+r4)+(r4+r4)]
    let r6 := F ones ![v 2,(1 : M)+(r5+r5)+(r5+r5)]
    let r7 := F ones ![v 1,(1 : M)+(r6+r6)+(r6+r6)]
    let r8 := F ones ![v 0,(1 : M)+(r7+r7)+(r7+r7)]
    F sourceFileCode (updated args) = r8+r8 := by
  dsimp only
  let v := physicalArgs args
  let suffix := F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]]
  let phys := physicalArgs (updated args)
  have hphys : phys = Function.update (Function.update v 8 (v 8+1)) 10 suffix := by
    funext i
    fin_cases i <;> simp [phys,updated,physicalArgs,inputOrder,v,suffix]
  have h := fileHalfCorrect 9 phys
  rw [←modelSourceFile,hphys] at h
  have htail := blockAsOnes (v 9) suffix
  rw [htail]
  exact h
def wrap (v : Fin 11 → M) (tail : M) : M :=
  let r0 := F ones ![v 8+1,(1 : M)+tail+tail]
  let r1 := F ones ![v 7,(1 : M)+(r0+r0)+(r0+r0)]
  let r2 := F ones ![v 6,(1 : M)+(r1+r1)+(r1+r1)]
  let r3 := F ones ![v 5,(1 : M)+(r2+r2)+(r2+r2)]
  let r4 := F ones ![v 4,(1 : M)+(r3+r3)+(r3+r3)]
  let r5 := F ones ![v 3,(1 : M)+(r4+r4)+(r4+r4)]
  let r6 := F ones ![v 2,(1 : M)+(r5+r5)+(r5+r5)]
  let r7 := F ones ![v 1,(1 : M)+(r6+r6)+(r6+r6)]
  F ones ![v 0,(1 : M)+(r7+r7)+(r7+r7)]

theorem outputWithCarry (args : Fin 11 → M) :
    let v := physicalArgs args
    let e := PA194Site29SeedTailRoundTrip.ext (v 9)
    let vv := e ⟨26,by decide⟩
    let ss := ((1 : M)+1)+1
    let qq := ss+ss
    let ww := F ones ![vv,(1 : M)+qq+qq]
    let tt := ww+ww
    let vals : Fin 27 → M := fun i => e i.castSucc
    let out := F (returnCode 26) (Fin.cases tt vals)
    F sourceFileCode (updated args) = wrap v out+wrap v out := by
  dsimp only
  let v := physicalArgs args
  let e := PA194Site29SeedTailRoundTrip.ext (v 9)
  let vv := e ⟨26,by decide⟩
  let ss := ((1 : M)+1)+1
  let qq := ss+ss
  let ww := F ones ![vv,(1 : M)+qq+qq]
  let tt := ww+ww
  let vals : Fin 27 → M := fun i => e i.castSucc
  let out := F (returnCode 26) (Fin.cases tt vals)
  let tail := F block ![v 9,F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]]]
  have ht := PA194Site29SeedOutput.seedReturnFile (M := M) (v 9)
  dsimp only at ht
  change out = tail at ht
  have h := outputFile args
  dsimp only at h
  change F sourceFileCode (updated args) = wrap v tail+wrap v tail at h
  have hw := congrArg (wrap v) ht
  exact h.trans (congrArg (fun x => x+x) hw.symm)
#print axioms outputWithCarry
#print axioms fileHalfCorrect
#print axioms outputFile
#print axioms blockAsOnes
end models
end PA194Site29OutputWithCarry
