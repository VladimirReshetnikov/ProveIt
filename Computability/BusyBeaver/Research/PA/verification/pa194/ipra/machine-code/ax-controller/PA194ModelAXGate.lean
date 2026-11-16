import PA194ModelAXCompare
import PA194ModelMPTransfer
import PA194AXGateRows
import PA194MachineAXCode

/-! The last AX source instructions, including the jump back to scheduler site
25, on arbitrary register values in a model of PRA with IΣ₁ induction. -/

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
set_option linter.unusedSectionVars false

namespace PA194ModelAXGate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelAXCompare PA194AXGateRows
open PA194ModelMPTransfer PA194ModelMPCompare PA194TargetGate

theorem rows3523 : CompareRows 3523 :=
  ⟨by decide,s3523,s3524,s3525,s3526,s3527,s3528,s3529,s3530,s3531,s3532,s3533,s3534⟩

theorem rows3541 : CompareRows 3541 :=
  ⟨by decide,s3541,s3542,s3543,s3544,s3545,s3546,s3547,s3548,s3549,s3550,s3551,s3552⟩

theorem rows3535 : TransferRows 3535 3538 7 6 := ⟨by decide,s3535,s3536,s3537⟩

theorem rows3538 : TransferRows 3538 3541 4 5 := ⟨by decide,s3538,s3539,s3540⟩

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def copied (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update (Function.update a 3 0) 6 (a 6+a 3)) 7 (a 7+a 3)

theorem copyOut (a : Fin 11 → M) : argsAfter a 3 [7,6] (a (location 3)) = copied a := by
  funext i
  fin_cases i <;> simp [argsAfter,copied,location,tally,subSelf,
    show modelNumeral M 0 = (0:M) from rfl,PA194StateOne.modelNumeralOne]

theorem copyA (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState 3519 a tail) (sourceState 3523 (copied a) tail) := by
  have path : Increments 3519 3520 [7,6] :=
    .inc _ _ _ _ (by decide) s3520 <|
    .inc _ _ _ _ (by decide) s3521 <|
    .jump _ (by decide) s3522
  have h := drain 3519 3520 3523 3 [7,6] (by decide) s3519 path (by decide) a tail
  rwa [copyOut] at h

noncomputable def result (a : Fin 11 → M) : Fin 11 → M := by
  classical
  exact Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update a 1
      (if a 4 = a 3 ∨ a 5 = a 3 then 0 else a 1)) 3 0) 4 0) 5 0) 6 0) 7 0

theorem gate (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive (sourceState 3519 a tail) (sourceState 3660 (result a) tail) := by
  classical
  let b := copied a
  let c := output b
  let d := transferArgs c 7 6
  let e := transferArgs d 4 5
  have hb := copyA a tail
  have hc := compare 3523 rows3523 b tail
  have hd := transfer 3535 3538 7 6 rows3535 (by decide) c tail
  have he := transfer 3538 3541 4 5 rows3538 (by decide) d tail
  have hf := compare 3541 rows3541 e tail
  have hout : output e = result a := by
    funext i
    fin_cases i <;>
      by_cases hd : a 4 = a 3 <;> by_cases hh : a 5 = a 3 <;>
      simp [e,d,c,b,copied,output,values,transferArgs,location,result,hx,hy,hd,hh]
  rw [hout] at hf
  have hj := PA194SourceFetchLoop.sourceJump 3553 3660 (by decide) s3553 (result a) tail
  exact appendPositive (append (append (append (append hb.reaches hc.reaches) hd.reaches)
    he.reaches) hf.reaches) (oneStep hj)

theorem returnToDispatch (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive (sourceState 3519 a tail) (sourceState 25 (result a) tail) := by
  exact appendPositive (gate a tail hx hy).reaches <| oneStep <|
    PA194SourceFetchLoop.sourceJump 3660 25 (by decide) s3660 (result a) tail

theorem resultTop (a : Fin 11 → M) (ht : a 1 = oldBundleValue (a 5) (a 4) (a 3)) :
    result a 1 = PA194MachineStack.axTop (a 5) (a 4) (a 3) := by
  simp [result,PA194MachineStack.axTop,ht]

theorem resultKeeps (a : Fin 11 → M) (i : Fin 11)
    (hi : i = 0 ∨ i = 2 ∨ i = 8 ∨ i = 9 ∨ i = 10) : result a i = a i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [result]

theorem resultClears (a : Fin 11 → M) (i : Fin 11)
    (hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) : result a i = 0 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [result]

#print axioms returnToDispatch
#print axioms resultTop
end models
end PA194ModelAXGate
