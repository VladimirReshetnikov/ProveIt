import PA194Site29SeedTailRoundTrip
import PA194Site28SeedOutput
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29SeedOutput
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning PA194UnaryRuns PA194Site28SeedTail PA194StartupSourceFrame PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem seedReturnFile (spare : M) :
    let e := PA194Site29SeedTailRoundTrip.ext spare
    let v := e ⟨26,by decide⟩
    let ss := ((1 : M)+1)+1
    let qq := ss+ss
    let ww := F ones ![v,(1 : M)+qq+qq]
    let tt := ww+ww
    let vals : Fin 27 → M := fun i => e i.castSucc
    F (returnCode 26) (Fin.cases tt vals) =
      F block ![spare,F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]]] := by
  dsimp only
  let e := PA194Site29SeedTailRoundTrip.ext spare
  let v := e ⟨26,by decide⟩
  let ss := ((1 : M)+1)+1
  let qq := ss+ss
  let ww := F ones ![v,(1 : M)+qq+qq]
  let tt := ww+ww
  let vals : Fin 27 → M := fun i => e i.castSucc
  let e25 := PA194Site28SeedTailRoundTrip.ext (1 : M)
  let vals25 : Fin 26 → M := fun i => e25 i.castSucc
  have hv : v = e25 ⟨25,by decide⟩ := by rfl
  have hvals : (fun i : Fin 26 => vals i.succ) = vals25 := by
    funext i
    fin_cases i <;> rfl
  have h := modelReturnCodeSucc (M := M) 25 (Fin.cases tt vals)
  dsimp only at h
  change F (returnCode 26) (Fin.cases tt vals) =
    F ones ![spare,F (returnCode 25) (Fin.cases tt (fun i : Fin 26 => vals i.succ))+
      F (returnCode 25) (Fin.cases tt (fun i : Fin 26 => vals i.succ))+1]+
    F ones ![spare,F (returnCode 25) (Fin.cases tt (fun i : Fin 26 => vals i.succ))+
      F (returnCode 25) (Fin.cases tt (fun i : Fin 26 => vals i.succ))+1] at h
  rw [hvals] at h
  have h25 := PA194Site28SeedOutput.seedReturnFile (M := M) (1 : M)
  dsimp only at h25
  change F (returnCode 25) (Fin.cases tt vals25) =
    F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]] at h25
  rw [h25,modelReturnBlock] at h
  exact h
#print axioms seedReturnFile
end models
end PA194Site29SeedOutput
