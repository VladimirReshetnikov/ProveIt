import PA194Site29ScanTo1
import PA194Site28IncrementWrite
import PA194RegisterPermutation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ThirdToIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194Site29TwoFile PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem thirdToIncrement (k l : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let tail := F ones ![v 9+1,v 10]
    let q := F ones ![v 8,tail+tail]
    let e : Fin 7 → M := ![v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
    let file := F (fileCode 6) e
    let w1 := F ones ![v 1,(1 : M)+file+file]
    let w0 := F ones ![v 0,(1 : M)+(w1+w1)+(w1+w1)]
    let a := F ones ![k,l]
    let a1 := a+a+1
    let a2 := a1+a1
    let a3 := a2+a2+1
    let z := F ones ![v 0,a3]
    let b := (z+z)+(z+z)+1
    let left := finalLeft 6 (v 1) b e
    let count := finalCount 6 (v 1) e
    let x := F ones ![count,left]
    let targetLeft := (x+x)+(x+x)+1
    let clock := (((((k+modelNumeral M 2)+modelNumeral M 1)+((v 0+modelNumeral M 2)))+
      fileClock 6 (v 1) e)+count)+modelNumeral M 2
    F PA194Stepper.stepper ![clock+(v 8+1),F pairCode ![modelNumeral M 2,
      F pairCode ![l,F ones ![k,(1 : M)+(w0+w0)+(w0+w0)]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![F ones ![v 8+1,targetLeft],tail]] := by
  dsimp only
  let v := physicalArgs args
  let tail := F ones ![v 9+1,v 10]
  let q := F ones ![v 8,tail+tail]
  let e : Fin 7 → M := ![v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
  let a := F ones ![k,l]
  let a1 := a+a+1
  let a2 := a1+a1
  let a3 := a2+a2+1
  let z := F ones ![v 0,a3]
  let b := (z+z)+(z+z)+1
  let left := finalLeft 6 (v 1) b e
  let count := finalCount 6 (v 1) e
  let x := F ones ![count,left]
  let targetLeft := (x+x)+(x+x)+1
  let clock := (((((k+modelNumeral M 2)+modelNumeral M 1)+((v 0+modelNumeral M 2)))+
      fileClock 6 (v 1) e)+count)+modelNumeral M 2
  have scan := PA194Site29ScanTo1.scanTo1 k (v 0) (v 1) l q e rfl
  dsimp only at scan
  rw [modelNumeralOne] at scan
  have write := PA194Site28IncrementWrite.incrementWrite (v 8) targetLeft tail
  change F PA194Stepper.stepper ![F addCode ![clock,v 8+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  dsimp only [clock]
  rw [modelNumeralOne,scan]
  change F PA194Stepper.stepper ![v 8+1,F pairCode ![(1 : M),F pairCode ![targetLeft,q]]] = _
  exact write
#print axioms thirdToIncrement
end models
end PA194Site29ThirdToIncrement
