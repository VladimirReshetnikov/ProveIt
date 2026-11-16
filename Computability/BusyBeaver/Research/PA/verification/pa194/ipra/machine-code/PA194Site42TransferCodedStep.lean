import PA194Site42TransferClockCode
import PA194SourceSite42TransferStep
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace PA194Site42TransferCodedStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

def input (k count m : M) (args : Fin 11 → M) : Fin 14 → M :=
  ![k,count,m,args 0,args 1,args 2,args 3,args 4,args 5,args 6,args 7,args 8,args 9,args 10]

theorem inputArgs (k count m : M) (args : Fin 11 → M) :
    PA194Site42TransferClockCode.inputArgs (input k count m args) = args := by
  funext i
  fin_cases i <;> rfl

theorem codedStep (k count tail m : M) (args : Fin 11 → M) (hm : args 7 = m+1)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let a := Function.update args 7 m
    let out := PA194Site43OutputFile.updated a count
    F step ![F step ![F step ![sourceState 42 args tail]]] = sourceState 42 out tail ∧
    F PA194Stepper.stepper ![F PA194Site42TransferClockCode.clockCode (input k count m args),physicalFrame 42 ((k+1)+1) args] =
      physicalFrame 42 (((k+1)+1)+1) out := by
  dsimp only
  let a := Function.update args 7 m
  let out := PA194Site43OutputFile.updated a count
  have hea : physicalArgs a 10 = F repeatOutput ![count,(0 : M)] := by
    change Function.update args 7 m 10 = _
    rw [Function.update_of_ne (by decide)]
    exact he
  have hc := PA194Site42TransferClockCode.modelClock (input k count m args)
  change F PA194Site42TransferClockCode.clockCode (input k count m args) =
    PA194Site42PositiveClockExact.clock k (PA194Site42TransferClockCode.inputArgs (input k count m args)) +
      PA194Site43ClockExact.clock k count (Function.update (PA194Site42TransferClockCode.inputArgs (input k count m args)) 7 m) + modelNumeral M 36 at hc
  rw [inputArgs] at hc
  have hp42 := PA194Site42PositiveClockExact.exactClock k m args hm
  have hp43 := PA194Site43ClockExact.exactClock k count a hea
  have hp44 := (PA194SourceSite44Physical.sourcePhysical ((k+1)+1) tail out).2
  obtain ⟨_,_,hsource,_⟩ := PA194SourceSite42TransferStep.transferStep k count tail m args hm he
  refine ⟨hsource,?_⟩
  rw [hc]
  change F PA194Stepper.stepper ![F addCode ![F addCode ![PA194Site42PositiveClockExact.clock k args,
    PA194Site43ClockExact.clock k count a],modelNumeral M 36],_] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hp42,hp43,hp44]
#print axioms inputArgs
#print axioms codedStep
end models
end PA194Site42TransferCodedStep
