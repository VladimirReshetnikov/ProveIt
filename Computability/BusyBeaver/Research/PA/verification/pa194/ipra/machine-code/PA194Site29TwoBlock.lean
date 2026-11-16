import PA194Site28ScanTo1
import PA194OnesCommute
import PA194RegisterFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29TwoBlock
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile TableDispatch PA194Site28ScanTo1 PA194UnaryRuns PA194OnesCommute PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem traverse (n l v t : M) :
    let w := F ones ![v,(1 : M)+t+t]
    let z := F ones ![v,t]
    let a := F ones ![n,l]
    F PA194Stepper.stepper ![n+modelNumeral M 2,F pairCode ![modelNumeral M 2,
      F pairCode ![l,F ones ![n,w+w]]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(a+a)+(a+a)+1,z]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let w := F ones ![v,(1 : M)+t+t]
  let z := F ones ![v,t]
  let a := F ones ![n,l]
  have hw : w = z+z+1 := by
    dsimp only [w,z]
    have ht : (1 : M)+t+t = (t+t)+1 := by simp only [add_assoc,add_comm]
    rw [ht,modelOnesCommute]
  have hs := PA194TwoScanInvariant.modelFullScan n l (w+w)
  have h0 := row0one (M := M) (a+a) z
  rw [←hw] at h0
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 0,F pairCode ![a+a,w]]) = _ at h0
  change F PA194Stepper.stepper ![F addCode ![n,modelNumeral M 2],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hs]
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,row2zero,h0]
theorem fileHop (m : Nat) (n l : M) (e : Fin (m+2) → M) :
    let rest := F (fileCode m) (fun i => e i.succ)
    let a := F ones ![n,l]
    F PA194Stepper.stepper ![n+modelNumeral M 2,F pairCode ![modelNumeral M 2,
      F pairCode ![l,F ones ![n,F (fileCode (m+1)) e]]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(a+a)+(a+a)+1,F ones ![e 0,rest]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let rest := F (fileCode m) (fun i => e i.succ)
  let w := F ones ![e 0,(1 : M)+rest+rest]
  have hword : F ones ![e 0+1,rest] = w := by
    dsimp only [w]
    rw [show e 0+1 = F Code.succ (fun _ => e 0) from modelAddOne _,modelOnesSucc]
    have hr : (1 : M)+rest+rest = rest+rest+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [hr,modelOnesCommute]
  have hw : F (fileCode (m+1)) e = w+w := by
    rw [modelFileSucc,modelBlock,hword]
  rw [hw]
  exact traverse n l (e 0) rest
#print axioms fileHop
#print axioms traverse
end models
end PA194Site29TwoBlock
