import PA194AX11HMPPrepValues
import PA194AX11HCompareExit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HMPSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPPush PA194ModelMPField PA194ModelMPImp PA194ModelMPTransfer PA194ModelMPDrain
open PA194TargetCantor PA194MachineProjections PA194IteratedSimulation PA194ControllerRunAdd
open Classical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact ordinary no-push MP output in the 11-register source frame. -/
def output (a : Fin 11 → M) : Fin 11 → M :=
  let d := a 4 + F fixedFirst ![a 8]
  let t := if impValue (a 1) d = a 5 then d else 0
  Function.update (Function.update (Function.update (Function.update (Function.update a 1 t) 4 d) 5 0) 6 0) 8 (F fixedSecond ![a 8])

theorem output_eq (a : Fin 11 → M) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194AX11HCompareExit.result (PA194PausedPrep.result (pushed (fieldArgs a)) (a 1) (a 2)) = output a := by
  funext i
  by_cases he : impValue (a 1) (a 4 + F fixedFirst ![a 8]) = a 5
  · fin_cases i <;> simp [PA194AX11HCompareExit.result,PA194ModelMPCompare.values,
      PA194PausedPrep.result,implicationArgs,transferArgs,location,pushed,fieldArgs,output,hx,hy,he]
  · have he' : a 5 ≠ impValue (a 1) (a 4 + F fixedFirst ![a 8]) := Ne.symm he
    fin_cases i <;> simp [PA194AX11HCompareExit.result,PA194ModelMPCompare.values,
      PA194PausedPrep.result,implicationArgs,transferArgs,location,pushed,fieldArgs,output,hx,hy,he,he']

/-- Exact candidate MP command from field-reader entry to dispatch return. -/
theorem mp_source (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3572 a tail] = sourceState 25 (output a) tail := by
  obtain ⟨m,hm⟩ := PA194AX11HMPPrep.mp_to_compare a tail hx hy
  obtain ⟨n,hn⟩ := PA194AX11HCompareExit.compareAndReturn
    (PA194PausedPrep.result (pushed (fieldArgs a)) (a 1) (a 2)) tail
  rw [output_eq a hx hy] at hn
  refine ⟨m+n,?_⟩
  rw [iterateAdd,hm,hn]

#print axioms output_eq
#print axioms mp_source
end models
end PA194AX11HMPSource
