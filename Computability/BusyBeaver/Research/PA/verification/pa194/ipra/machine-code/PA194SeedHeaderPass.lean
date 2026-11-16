import PA194SeedHeaderReturn
import PA194SeedHeaderTo21
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedHeaderPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PA194SeedHeaderTo21 PA194SeedHeaderReturn PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- First seeded source-header pass from root to root, with arbitrary
model-valued file and header length. The exact transformed file is retained. -/
theorem sourceHeaderPass (k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let r := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let s := F zeros ![k,f+f+1]
    let y0 := s+s
    let y1 := y0+y0
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let t := (1 : M)+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))
    let w := F ones ![k+1,t]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let w4 := w3+w3
    let w5 := w4+w4
    let w6 := w5+w5
    let c0 := (modelNumeral M 12 + (((((k+1)+1)+1)+1)+((k+1)+1))) + modelNumeral M 4
    let c1 := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![c0+c1,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),y6+y6+1]]] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),w6+1]] := by
  dsimp only
  let v := physicalArgs e
  let r := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let t := (1 : M)+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))
  let w := F ones ![k+1,t]
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let w4 := w3+w3
  let w5 := w4+w4
  let c0 := (modelNumeral M 12 + (((((k+1)+1)+1)+1)+((k+1)+1))) + modelNumeral M 4
  let c1 := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h21 := sourceHeaderTo21 (1 : M) k e
  dsimp only at h21
  have hret := returnTo24 w5
  dsimp only at hret
  change F PA194Stepper.stepper ![F addCode ![c0,c1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h21,hret]
#print axioms sourceHeaderPass
end models
end PA194SeedHeaderPass
