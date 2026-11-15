import PA194PrefixFile
import PA194IncrementFront
import PA194GenericRightScan
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31SelectedThrough
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194IncrementFront
open PA194StateOne PA194RightRows TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Scan a model-valued unary prefix, six untouched file blocks, the marked
selected block, and three following file blocks. The final suffix is arbitrary. -/
theorem selectedThrough (k l : M) (ep : Fin 7 → M) (e : Fin 5 → M)
    (hp : ep 6 = F (markedFile 3) e) :
    let pl := F (PA194PrefixFile.leftCode 6) (Fin.cases (F ones ![k,l]) ep)
    let front := (((1 : M)+1)+e 0)+F (costCode 3) (fun i => e i.succ)
    F PA194Stepper.stepper ![(k+F (costCode 6) ep)+front,
      F pairCode ![modelNumeral M 2,F pairCode ![l,F ones ![k,F (fileCode 6) ep]]]] =
    F pairCode ![(1 : M),F pairCode ![F (leftCode 3)
      (Fin.cases (F ones ![e 0,(pl+pl)+(pl+pl)+1]) (fun i => e i.succ)),e 4]] := by
  dsimp only
  have hloop (x y : M) : F PackedClock.encodedStep
      (fun _ => F pairCode ![modelNumeral M 2,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 2,F pairCode ![x+x+1,y]] := by
    have h := rightOne 2 1 2 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h
  have hscan := PA194GenericRightScan.modelFullScan 2 hloop k l (F (fileCode 6) ep)
  have hf := PA194PrefixFile.modelPrefixFile 6 ep (F ones ![k,l])
  change ep (Fin.last 6) = F (markedFile 3) e at hp
  rw [hp] at hf
  have hs := modelSelectedAndCarry 3 e (F (PA194PrefixFile.leftCode 6) (Fin.cases (F ones ![k,l]) ep))
  change F PA194Stepper.stepper ![F addCode ![F addCode ![k,F (costCode 6) ep],_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![k,F (costCode 6) ep],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan,hf,hs]
  rfl
#print axioms selectedThrough
end models
end PA194Site31SelectedThrough
