import PA194RewindFirst
import PA194FileTraversal
import PA194MarkerReturnCell
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194RewindFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194BinaryDouble PA194CarryFile
open PA194MarkerReturnCell PA194ReturnFileMeaning PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- A regular finite file ending with twice an odd value is itself twice an
odd value, uniformly over all candidate PRA models. -/
theorem fileDoubleOdd (n : Nat) (e : Fin (n+1) → M) (b : M)
    (ht : e (Fin.last n) = (b+b+1)+(b+b+1)) :
    ∃ z : M, F (fileCode n) e = (z+z+1)+(z+z+1) := by
  cases n with
  | zero =>
    refine ⟨b,?_⟩
    rw [fileCode,modelProjection]
    exact ht
  | succ n =>
    let tail := F (fileCode n) (fun i => e i.succ)
    refine ⟨F ones ![e 0,tail],?_⟩
    rw [modelFileSucc,modelBlock]
    have h : F ones ![e 0+1,tail] = F ones ![e 0,tail]+F ones ![e 0,tail]+1 := by
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],tail] = _
      rw [modelAddOne,modelOnesSucc]
    rw [h]
/-- Rewind a fixed finite left file through state 17. Its final left tail is
twice an odd value; all register values and times may be nonstandard. -/
theorem rewindFile (n : Nat) (e : Fin (n+1) → M) (b t : M)
    (ht : e (Fin.last n) = (b+b+1)+(b+b+1)) :
    let f := F (fileCode n) e
    let out := F (PA194FileTraversal.leftCode n) (Fin.cases t e)
    F PA194Stepper.stepper ![F (costCode n) e,F pairCode ![modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => F halfCode (fun _ => f)),t+t+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing t with
  | zero =>
    dsimp only
    change e 0 = (b+b+1)+(b+b+1) at ht
    rw [modelCostZero]
    have hz := PA194Stepper.modelStepperZero (F pairCode ![modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => F halfCode (fun _ => F (fileCode 0) e)),t+t+1]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
    rw [hz,PA194FileTraversal.modelLeftZero]
    change F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => F halfCode (fun _ => F (.proj 0) e)),t+t+1]] = _
    rw [modelProjection,ht,(modelDouble (b+b+1)).2,(modelOdd b).2]
    simp only [Fin.cases_zero,add_assoc,add_comm]
  | succ n ih =>
    dsimp only
    let rest : Fin (n+1) → M := fun i => e i.succ
    have hlast : rest (Fin.last n) = (b+b+1)+(b+b+1) := by exact ht
    obtain ⟨z,hz⟩ := fileDoubleOdd n rest b hlast
    let t1 := F block ![e 0,t]
    have hfile : F (fileCode (n+1)) e = F block ![e 0,(z+z+1)+(z+z+1)] := by
      rw [modelFileSucc,hz]
    have hl : F halfCode (fun _ => F halfCode (fun _ => F (fileCode (n+1)) e)) =
        F ones ![e 0,(z+z+1)+(z+z+1)] := by
      rw [hfile,modelBlock,(modelDouble _).2]
      have hs : F ones ![e 0+1,(z+z+1)+(z+z+1)] =
          F ones ![e 0,(z+z+1)+(z+z+1)]+F ones ![e 0,(z+z+1)+(z+z+1)]+1 := by
        change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
        rw [modelAddOne,modelOnesSucc]
      rw [hs,(modelOdd _).2]
    have hm := modelMarkerReturnCell ⟨1,by decide⟩ (e 0) (z+z+1) t
    dsimp only at hm
    rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl,
      (modelOdd z).1,(modelOdd z).2] at hm
    have htcomm : (1 : M)+t+t = t+t+1 := by simp only [add_assoc,add_comm]
    rw [htcomm,modelReturnBlock] at hm
    have hc : ((1 : M)+1)+e 0 = (e 0+1)+1 := by simp only [add_assoc,add_comm]
    have hr := ih rest t1 hlast
    dsimp only at hr
    rw [hz,(modelDouble (z+z+1)).2,(modelOdd z).2] at hr
    have hs : (1 : M)+t1+t1 = t1+t1+1 := by simp only [add_comm,add_left_comm]
    rw [hs] at hm
    rw [modelCostSucc,hc,hl]
    change F PA194Stepper.stepper ![F addCode ![(e 0+1)+1,F (costCode n) rest],_] = _
    rw [PA194StepperCompose.modelStepperCompose,hm,hr,PA194FileTraversal.modelLeftSucc]
    rfl
#print axioms rewindFile
#print axioms fileDoubleOdd
end models
end PA194RewindFile
