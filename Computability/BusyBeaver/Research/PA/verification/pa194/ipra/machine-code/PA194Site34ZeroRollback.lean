import PA194Site34ZeroFile
import PA194CarryOneAppendZero
import PA194RollbackFile
import PA194Site27ZeroTo11
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34ZeroRollback
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning PA194Site34ZeroFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194StateOne PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def before (k : M) : M := F ones ![k+1,modelNumeral M 800]
noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  F addCode ![F addCode ![PA194Site34Branch.clock k args,modelNumeral M 2],F (PA194CarryFile.costCode 2) (vec args)]

theorem zeroRollback (k : M) (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
        F parityCode (fun _ => before k)+F sourceFileCode args+F sourceFileCode args]] := by
  let e := physicalArgs args
  let t := tailWord args
  let u := F ones ![e 2,F (fileCode 7) (fun i => e i.succ.succ.succ)]
  let q := F ones ![(0 : M),t+t]
  let c := (q+q)+(q+q)
  let v1 : Fin 2 → M := ![e 0,c]
  let carried := F (PA194CarryFile.leftCode 1) (Fin.cases (before k) v1)
  let z := carried+carried+1
  have ht : t = u+u+1 := by
    dsimp only [t,tailWord,u]
    rw [show e 2+1 = F Code.succ (fun _ => e 2) from modelAddOne _,modelOnesSucc]
  have hv : physicalArgs args 1 = (0 : M) := hz
  have htail : PA194Site34Branch.selectedTail args = t+t := by
    exact (tailIdentity args).symm
  have hm : PA194Site34Branch.marker k args = z := by
    dsimp only [PA194Site34Branch.marker,z,carried,v1,c,q,before]
    rw [hv,htail]
  have h5 := PA194Site34Branch.zeroTo5 k args hz
  dsimp only at h5
  change F PA194Stepper.stepper ![PA194Site34Branch.clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 5,F pairCode ![(PA194Site34Branch.marker k args+PA194Site34Branch.marker k args)+
        (PA194Site34Branch.marker k args+PA194Site34Branch.marker k args)+1,t]] at h5
  rw [hm] at h5
  have h11 := PA194Site27ZeroTo11.fiveTo11 z u
  dsimp only at h11
  rw [←ht] at h11
  have hc := PA194CarryOneAppendZero.oneThenZero (before k) (e 0) c
  dsimp only at hc
  change F (PA194CarryFile.leftCode 2) (Fin.cases (before k) (vec args)) = z+z at hc
  have hr := PA194RollbackFile.modelRollbackPrefix 2 (vec args) (before k) (t+t)
  dsimp only at hr
  rw [hc,(modelDouble z).1,(modelDouble z).2] at hr
  simp only [zero_add] at hr
  change F PA194Stepper.stepper ![F (PA194CarryFile.costCode 2) (vec args),
      F pairCode ![modelNumeral M 11,F pairCode ![z,(t+t)+(t+t)]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
      F parityCode (fun _ => before k)+returned args+returned args]] at hr
  rw [returnedIsSourceFile args hz] at hr
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h5,h11,hr]
#print axioms zeroRollback
end models
end PA194Site34ZeroRollback
