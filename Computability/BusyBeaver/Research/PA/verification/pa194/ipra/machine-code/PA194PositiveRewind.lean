import PA194SixScanInvariant
import PA194StepperCompose
import PA194IncrementTail
import PA194LeftOneWriteOne
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PositiveRewind
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194SixScanInvariant PA194IncrementTail PA194LeftOneWriteOne
open PRAExhaustion PA194BinaryDouble PA194UnaryRuns BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem positiveRewind (n l r : M) :
    let file := r+r+1
    let output := F ones ![n,file]+F ones ![n,file]
    F PA194Stepper.stepper ![n+1,F pairCode ![modelNumeral M 7,
      F pairCode ![F ones ![n,l+l],file]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![l,output]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have hex := modelZeroOrSuccPred n
  change n = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => n)) = n at hex
  rcases hex with hn | hn
  · subst n
    simp only [zero_add,modelOnesZero]
    nth_rewrite 1 [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,packedSeven]
  · let p := F predCode (fun _ => n)
    have hp : n=p+1 := by
      have ha : F Code.succ (fun _ => p) = p+1 := (modelAddOne p).symm
      exact hn.symm.trans ha
    rw [hp]
    let a := F ones ![p,l+l]
    let file := r+r+1
    have hnones : F ones ![p+1,l+l] = a+a+1 := by
      change F ones ![F addCode ![p,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    have hfones : F ones ![p+1,file] = F ones ![p,file]+F ones ![p,file]+1 := by
      change F ones ![F addCode ![p,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    have h7 := leftOneWriteOne 7 6 (by decide) (by decide +kernel) (a+a+1) r
    rw [(modelOdd a).1,(modelOdd a).2] at h7
    have h7' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 7,F pairCode ![a+a+1,file]]) =
        F pairCode ![modelNumeral M 6,F pairCode ![a,file+file+1]] := by
      convert h7 using 1 <;> dsimp [file] <;> simp only [add_assoc,add_comm,add_left_comm]
    have hs := modelFullScan p (l+l) file
    have h6 := leftOneWriteOne 6 6 (by decide) (by decide +kernel) (l+l) (F ones ![p,file])
    rw [(modelDouble l).1,(modelDouble l).2,zero_add] at h6
    have h6' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 6,F pairCode ![l+l,F ones ![p+1,file]]]) =
        F pairCode ![modelNumeral M 6,F pairCode ![l,F ones ![p+1,file]+F ones ![p+1,file]]] := by
      rw [hfones]
      convert h6 using 1 <;> simp only [add_assoc,add_comm,add_left_comm]
    rw [hnones]
    have hclock : (p+1)+1 = ((1 : M)+p)+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [hclock]
    change F PA194Stepper.stepper ![F addCode ![(1 : M)+p,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
    change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![(1 : M),p],_]) = _
    rw [PA194StepperCompose.modelStepperCompose]
    have hstep : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 7,F pairCode ![a+a+1,file]]] =
        F pairCode ![modelNumeral M 6,F pairCode ![a,file+file+1]] := by
      nth_rewrite 1 [←modelNumeralOne]
      change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
      rw [PA194Stepper.modelStepperSucc,
        show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
        PA194Stepper.modelStepperZero,h7']
    rw [hstep,hs,h6']
#print axioms positiveRewind
end models
end PA194PositiveRewind
