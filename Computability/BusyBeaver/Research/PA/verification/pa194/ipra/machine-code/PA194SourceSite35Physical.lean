import PA194Site35Complete
import PA194SourceSite35Controller
import PA194Site35ToHeaderReturn
import PA194Site35HeaderReturn
import PA194Site35OutputFile
import PA194Site32ZeroPath
import PA194Site35To2
import PA194Site35MarkedFile
import PA194Site35IncrementReturn
import PA194Site35IncrementSelected
import PA194Site35ReturnPrefix
import PA194Site31Selected
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSite35Physical
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SourceControllerCode PA194SourceSite31Controller PA194ZeroRuns PA194Path27Header PA194BinaryDouble PA194FiniteControls PA194Site32ZeroPath PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194RightRows PA194StateOne PA194ReturnFile
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem sourcePhysical (t count controllerTail : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let k := t+1
    let d := modelNumeral M 804
    let v := physicalArgs args
    let e : Fin 6 → M := fun i => v ⟨i.val+5,by omega⟩
    let marked := F (markedFile 4) e
    let ep : Fin 6 → M := ![v 0,v 1,v 2,v 3,v 4,marked]
    let file := F (fileCode 5) ep
    let pl := F (PA194PrefixFile.leftCode 5) (Fin.cases (F ones ![k+1,d+d]) ep)
    let c := F (costCode 4) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 4) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 5) (Fin.cases result ep)
    let a := F ones ![k,(1 : M)+out+out]
    let outer : M → M := fun x =>
      F PA194Stepper.stepper ![modelNumeral M 24,
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,x]]]]
    F PA194SourceControllerCode.step ![sourceState 35 args controllerTail] =
      sourceState 36 (PA194Site35OutputFile.updated args count) controllerTail ∧
    outer (
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode 5) ep,
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 5) ep,
                      F PA194Stepper.stepper ![k+1,F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site35To14.clock k args,modelNumeral M 3],PA194Site35SecondTo17.backCost k args],modelNumeral M 25],modelNumeral M 10],
                        PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args]]]]]]]]]]]]] ) =
    PA194SourceSite31Physical.physicalFrame 36 t (PA194Site35OutputFile.updated args count) := by
  dsimp only
  have hc := PA194SourceSite35Controller.controllerStep args controllerTail
    (F repeatOutput ![F Code.succ (fun _ => count),(0 : M)])
  change F PA194SourceControllerCode.step ![sourceState 35 args controllerTail] =
    sourceState 36 (PA194Site35OutputFile.updated args count) controllerTail at hc
  exact ⟨hc,PA194Site35Complete.complete t count args he⟩
#print axioms sourcePhysical
end models
end PA194SourceSite35Physical
