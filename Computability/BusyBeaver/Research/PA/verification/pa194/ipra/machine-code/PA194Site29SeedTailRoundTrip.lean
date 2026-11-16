import PA194Site28SeedTailRoundTrip
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29SeedTailRoundTrip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Site28CarryFile PA194StartupSourceFrame BinaryTapeCodes TableDispatch PA194RegisterFile PA194UnaryRuns PA194Site28SeedTail PA194Site28CarryRoundTrip PA194Site28CarryCodes PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def ext (spare : M) : Fin 28 → M := Fin.cases spare (Fin.cases (1 : M) (fun i => modelNumeral M (spareValues i)))

theorem seedTailRoundTrip (spare l : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    let e := ext spare
    let v := e ⟨26,by decide⟩
    let a := carryLeft 26 l e
    let s := ((1 : M)+1)+1
    let q := s+s
    let w := F ones ![v,(1 : M)+q+q]
    let t := w+w
    let vals : Fin 27 → M := fun i => e i.castSucc
    let out := F (PA194ReturnFile.returnCode 26) (Fin.cases t vals)
    let seed := F block ![(1 : M),modelNumeral M seedTail]
    F PA194Stepper.stepper ![F (PA194CarryFile.costCode 26) vals,
      F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![(1 : M)+(v+1),
            F PA194Stepper.stepper ![F (timeCode 26) e,
              F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![spare+1,seed]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),out+out+1]] := by
  let e := ext spare
  have he : e (Fin.last 27) = (0 : M) := by
    change modelNumeral M (spareValues (Fin.last 25)) = (0 : M)
    rfl
  have h := PA194Site28CarryRoundTrip.roundTrip (M := M) 26 e l hl he
  have ht : F (fileCode 26) (fun i => e i.succ) = F block ![(1 : M),modelNumeral M seedTail] := by
    rw [modelFileSucc]
    change F block ![(1 : M),F (fileCode 25) (fun i => modelNumeral M (spareValues i))] = _
    rw [modelFileSeedTail]
  rw [ht] at h
  exact h
#print axioms seedTailRoundTrip
end models
end PA194Site29SeedTailRoundTrip
