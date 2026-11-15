import PA194Site28SeedOutputProbe
import PA194Site28SeedTailRoundTrip
import PA194RegisterFileStandard
import PA194StandardCodeBridge
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28SeedOutput
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StandardCodeBridge PA194RegisterFile PA194RegisterFileStandard PA194Site28SeedTail PA194Site28SeedTailRoundTrip PA194StartupSourceFrame PA194ReturnFile PA194ReturnFileMeaning PA194UnaryRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem fixedTail :
    F (returnCode 24) (Fin.cases (modelNumeral M 54) (fun _ => modelNumeral M 1)) =
      F block ![(1 : M),modelNumeral M seedTail] := by
  let a : Fin 26 → Nat := Fin.cases 54 (fun _ => 1)
  have h := (modelStandardCode (M := M) (returnCode 24)) a
  have ha : (fun i => modelNumeral M (a i)) = Fin.cases (modelNumeral M 54) (fun _ => modelNumeral M 1) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [ha] at h
  have hnat : Structure.func (L := language) (returnCode 24) a =
      Structure.func (L := language) block (![1,seedTail] : Fin 2 → Nat) := PA194Site28SeedOutputProbe.probe
  rw [hnat] at h
  have hb := (modelStandardCode (M := M) block) (![1,seedTail] : Fin 2 → Nat)
  have hv : (fun i => modelNumeral M ((![1,seedTail] : Fin 2 → Nat) i)) =
      ![(1 : M),modelNumeral M seedTail] := by
    funext i
    fin_cases i
    · change modelNumeral M 1 = (1 : M)
      exact modelNumeralOne
    · rfl
  rw [hv] at hb
  exact h.trans hb.symm

theorem tailBase :
    let s := ((1 : M)+1)+1
    let q := s+s
    let w := F ones ![(1 : M),(1 : M)+q+q]
    w+w = modelNumeral M 54 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have h13 : (1 : M)+(((1 : M)+1)+1+(((1 : M)+1)+1))+
      (((1 : M)+1)+1+(((1 : M)+1)+1)) = modelNumeral M 13 := by
    simp only [←modelNumeralOne,←modelNumeralAdd]
  rw [h13]
  have hw := (modelStandardCode (M := M) ones) (![1,13] : Fin 2 → Nat)
  have hv : (fun i => modelNumeral M ((![1,13] : Fin 2 → Nat) i)) = ![(1 : M),modelNumeral M 13] := by
    funext i
    fin_cases i
    · change modelNumeral M 1 = (1 : M); exact modelNumeralOne
    · rfl
  rw [hv,modelOnesNat] at hw
  change F ones ![(1 : M),modelNumeral M 13] = modelNumeral M 27 at hw
  rw [hw,←modelNumeralAdd]
theorem seedReturnFile (spare : M) :
    let e := PA194Site28SeedTailRoundTrip.ext spare
    let v := e ⟨25,by decide⟩
    let s := ((1 : M)+1)+1
    let q := s+s
    let w := F ones ![v,(1 : M)+q+q]
    let t := w+w
    let vals : Fin 26 → M := fun i => e i.castSucc
    F (returnCode 25) (Fin.cases t vals) = F block ![spare,F block ![(1 : M),modelNumeral M seedTail]] := by
  let e := PA194Site28SeedTailRoundTrip.ext spare
  let v := e ⟨25,by decide⟩
  let s := ((1 : M)+1)+1
  let q := s+s
  let w := F ones ![v,(1 : M)+q+q]
  let t := w+w
  let vals : Fin 26 → M := fun i => e i.castSucc
  have hv : v = (1 : M) := by
    change modelNumeral M 1 = (1 : M)
    exact modelNumeralOne
  have ht : t = modelNumeral M 54 := by
    dsimp only [t,w,q,s]
    rw [hv]
    exact tailBase
  have hvals : (fun i : Fin 25 => vals i.succ) = (fun _ => modelNumeral M 1) := by
    funext i
    fin_cases i <;> rfl
  have h := PA194ReturnFile.modelReturnCodeSucc (M := M) 24 (Fin.cases t vals)
  dsimp only at h
  change F (returnCode 25) (Fin.cases t vals) =
    F ones ![spare,F (returnCode 24) (Fin.cases t (fun i : Fin 25 => vals i.succ))+
      F (returnCode 24) (Fin.cases t (fun i : Fin 25 => vals i.succ))+1]+
    F ones ![spare,F (returnCode 24) (Fin.cases t (fun i : Fin 25 => vals i.succ))+
      F (returnCode 24) (Fin.cases t (fun i : Fin 25 => vals i.succ))+1] at h
  rw [hvals,ht,fixedTail,PA194ReturnFileMeaning.modelReturnBlock] at h
  change F (returnCode 25) (Fin.cases t vals) = _
  rw [ht]
  exact h
#print axioms seedReturnFile
#print axioms tailBase
#print axioms fixedTail
end models
end PA194Site28SeedOutput
