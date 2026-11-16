import PA194OneSpareFileRoundTrip
import PA194OneSpareSeed26
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194SeedFileRoundTrip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194OneSpareIterate PA194OneSpareReturn PA194OneSpareRoundTrip PA194OneSpareIdentities PA194Site28CarryCell PA194ReturnCell PA194UnaryRuns PA194BinaryDouble PA194RegisterFile PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem roundTrip (spare marked : M) (hl : F parityCode (fun _ => marked) = (1 : M)) :
    let n := modelNumeral M 26
    let inSuffix := F block ![(1 : M),modelNumeral M PA194StartupSourceFrame.seedTail]
    let outSuffix := F repeatOutput ![F Code.succ (fun _ => n),(0 : M)]
    let outFile := F block ![spare,outSuffix]
    F PA194Stepper.stepper ![(spare+1)+1,
      F PA194Stepper.stepper ![(n+n)+n,
        F PA194Stepper.stepper ![modelNumeral M 2,
          F PA194Stepper.stepper ![modelNumeral M 3,
            F PA194Stepper.stepper ![(n+n)+n,
              F PA194Stepper.stepper ![(1 : M)+(spare+1),
                F pairCode ![modelNumeral M 3,F pairCode ![marked,F ones ![spare+1,inSuffix]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => marked),outFile+outFile+1]] := by
  have h := PA194OneSpareFileRoundTrip.roundTrip (modelNumeral M 26) spare marked hl
  dsimp only at h ⊢
  rw [PA194OneSpareSeed26.modelSeed26] at h
  exact h
#print axioms roundTrip
end models
end PA194SeedFileRoundTrip
