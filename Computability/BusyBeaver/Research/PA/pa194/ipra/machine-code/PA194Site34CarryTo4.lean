import PA194Site32CarryTo4
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site34CarryTo4
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194UnaryRuns PA194OnesCommute PA194RegisterFile PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem carryTo4 (k l a u : M) :
    let c := (u+u)+(u+u)
    let w := F ones ![a,(1 : M)+c+c]
    let vec : Fin 2 → M := ![a,c]
    let before := F ones ![k+1,l]
    let left := F (PA194CarryFile.leftCode 1) (Fin.cases before vec)
    let z := left+left+1
    let time := ((k+1)+F (PA194CarryFile.costCode 1) vec)+modelNumeral M 2
    F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 1,
      F pairCode ![l,F ones ![k,(1 : M)+(w+w)+(w+w)]]]] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,u]] := by
  dsimp only
  let c := (u+u)+(u+u)
  let w := F ones ![a,(1 : M)+c+c]
  let vec : Fin 2 → M := ![a,c]
  let file := F (fileCode 1) vec
  let before := F ones ![k+1,l]
  let left := F (PA194CarryFile.leftCode 1) (Fin.cases before vec)
  let cost := F (PA194CarryFile.costCode 1) vec
  have hw : F ones ![a+1,c] = w := by
    have h := modelOnesCommute a c
    change F ones ![a,c+c+1] = _ at h
    rw [show a+1 = F Code.succ (fun _ => a) from modelAddOne _,modelOnesSucc]
    dsimp only [w]
    simpa only [add_assoc,add_comm,add_left_comm] using h.symm
  have hf : file = w+w := by
    dsimp only [file]
    rw [modelFileSucc,modelBlock]
    change F ones ![a+1,F (.proj 0) (fun i : Fin 1 => vec i.succ)]+
      F ones ![a+1,F (.proj 0) (fun i : Fin 1 => vec i.succ)] = w+w
    rw [modelProjection]
    change F ones ![a+1,c]+F ones ![a+1,c] = w+w
    rw [hw]
  have hon : F ones ![k,(1 : M)+(w+w)+(w+w)] = F ones ![k+1,file] := by
    have hsum : (1 : M)+(w+w)+(w+w) = (w+w)+(w+w)+1 := by ac_rfl
    rw [hsum,hf,modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],w+w]
    rw [modelAddOne,modelOnesSucc]
  rw [hon]
  have hs := PA194ScanInvariant.modelFullScan (k+1) l file
  have hc := PA194CarryFile.modelCarryFile 1 vec before
  change F PA194Stepper.stepper ![cost,F pairCode ![(1 : M),F pairCode ![before,file]]] =
    F pairCode ![(1 : M),F pairCode ![left,(u+u)+(u+u)]] at hc
  have h2 := PA194ThirdPassTo4.twoTo4 left u
  rw [modelNumeralOne] at h2 ⊢
  change F PA194Stepper.stepper ![F addCode ![(k+1)+cost,modelNumeral M 2],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 2,F PA194Stepper.stepper ![F addCode ![k+1,cost],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hs,hc,h2]
#print axioms carryTo4
end models
end PA194Site34CarryTo4
