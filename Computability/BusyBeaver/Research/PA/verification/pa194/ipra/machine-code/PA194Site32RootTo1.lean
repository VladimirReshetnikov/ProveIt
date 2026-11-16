import PA194Site32HeaderTo64
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32RootTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32HeaderTo64 PA194State42Boundary PA194Path27Header PA194UnaryRuns PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem rootTo1 (k q : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let w := F ones ![k+1,q]
    let c12 := F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)]
    F PA194Stepper.stepper ![F addCode ![c12,modelNumeral M 2],
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) (w+w)]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![((a6+a6)+(a6+a6))+((a6+a6)+(a6+a6)),F ones ![k,q]]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  have h12 := pathTo42 (1 : M) (F ones ![k+1,q]+F ones ![k+1,q])
  dsimp only at h12
  have h2 := positiveRun k (a6+a6) q
  dsimp only at h2
  rw [PA194StepperCompose.modelStepperCompose,h12,h2]
#print axioms rootTo1
end models
end PA194Site32RootTo1
