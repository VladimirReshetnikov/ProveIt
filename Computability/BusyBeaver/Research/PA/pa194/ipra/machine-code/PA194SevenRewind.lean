import PA194RewindFile
import PA194FileTraversalMeaning
import PA194RewindFirst
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SevenRewind
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194BinaryDouble PA194CarryFile
open PA194FileTraversalMeaning PA194RewindFirst PA194RewindFile PA194ReturnFileMeaning PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- Seven traversed blocks rewind from dense 14 to dense 17. The next
right-hand block's leading one is erased; all seven returned blocks retain
exactly their values and original order. -/
theorem sevenTo17 (e : Fin 8 → M) (b s : M) :
    let base := (b+b+1)+(b+b+1)
    let rev : Fin 7 → M := ![e 5,e 4,e 3,e 2,e 1,e 0,base]
    let left := F (PA194FileTraversal.leftCode 7) (Fin.cases base e)
    let tail := (s+s)+(s+s)
    let file := F (fileCode 7) ![e 0,e 1,e 2,e 3,e 4,e 5,e 6,tail]
    F PA194Stepper.stepper ![(modelNumeral M 2+((e 6+1)+1))+F (costCode 6) rev,
      F pairCode ![modelNumeral M 14,F pairCode ![left,s+s+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+file+file]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let base := (b+b+1)+(b+b+1)
  let rev : Fin 7 → M := ![e 5,e 4,e 3,e 2,e 1,e 0,base]
  let rest := F (fileCode 6) rev
  let l := F halfCode (fun _ => rest)
  let r := F ones ![e 6,(1 : M)+((s+s)+(s+s))+((s+s)+(s+s))]
  let t := F block ![e 6,(s+s)+(s+s)]
  have hrest : rest = l+l := by
    dsimp only [rest,l]
    rw [modelFileSucc,modelBlock,(modelDouble _).2]
  have hodd : F parityCode (fun _ => l) = (1 : M) := by
    dsimp only [l,rest]
    rw [modelFileSucc,modelBlock,(modelDouble _).2]
    have hx : F ones ![e 5+1,F (fileCode 5) (fun i => rev i.succ)] =
        F ones ![e 5,F (fileCode 5) (fun i => rev i.succ)]+F ones ![e 5,F (fileCode 5) (fun i => rev i.succ)]+1 := by
      change F ones ![F addCode ![e 5,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    change F parityCode (fun _ => F ones ![e 5+1,F (fileCode 5) (fun i => rev i.succ)]) = _
    rw [hx,(modelOdd _).1]
  have hleft : F (PA194FileTraversal.leftCode 7) (Fin.cases base e) = F block ![e 6,l+l] := by
    rw [leftSevenMeaning,modelFileSucc]
    rw [←hrest]
    have hv : (fun i : Fin 7 => (![e 6,e 5,e 4,e 3,e 2,e 1,e 0,base] : Fin 8 → M) i.succ) = rev := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rfl
  have hfirst := firstTo17 (e 6) l s
  dsimp only at hfirst
  rw [hodd] at hfirst
  have hrt : (r+r) = t := by
    dsimp only [r,t]
    have hc : (1 : M)+((s+s)+(s+s))+((s+s)+(s+s)) = ((s+s)+(s+s))+((s+s)+(s+s))+1 := by
      simp only [add_assoc,add_comm,add_left_comm]
    rw [hc,modelReturnBlock]
  change _ = F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),(1 : M)+(r+r)+(r+r)]] at hfirst
  rw [hrt] at hfirst
  have ht : rev (Fin.last 6) = (b+b+1)+(b+b+1) := rfl
  have hrev := rewindFile 6 rev b t ht
  dsimp only at hrev
  change F PA194Stepper.stepper ![F (costCode 6) rev,F pairCode ![modelNumeral M 17,
    F pairCode ![F halfCode (fun _ => F halfCode (fun _ => rest)),t+t+1]]] = _ at hrev
  rw [hrest,(modelDouble l).2] at hrev
  have hc : (1 : M)+t+t = t+t+1 := by simp only [add_comm,add_left_comm]
  rw [hc] at hfirst
  have hout : F (PA194FileTraversal.leftCode 6) (Fin.cases t rev) =
      F (fileCode 7) ![e 0,e 1,e 2,e 3,e 4,e 5,e 6,(s+s)+(s+s)] := by
    simp only [PA194FileTraversal.modelLeftSucc,PA194FileTraversal.modelLeftZero,
      modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    rfl
  rw [hout] at hrev
  rw [hleft]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2+((e 6+1)+1),F (costCode 6) rev],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hfirst,hrev]
#print axioms sevenTo17
end models
end PA194SevenRewind
