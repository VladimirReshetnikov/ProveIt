import PA194SchedulerHaltSource
import PA194SourceSchedulerOrbit
import PA194CompressedStartup

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194SchedulerSourceFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194MachineShiftMPCode
open PA194SchedulerFetchPositive PA194IteratedSimulation

open PA194SourceControllerCode (pc)
open PA194StartupSourceFrame (seedArgs)
open PA194CompressedStartup (initialSource startArgs)

private def fileCode (a : Fin 9 → Code 1) : Code 1 :=
  bin pairCode (a 0) (bin pairCode (a 1) (bin pairCode (a 2)
    (bin pairCode (a 3) (bin pairCode (a 4) (bin pairCode (a 5)
     (bin pairCode (a 6) (bin pairCode (a 7) (bin pairCode (a 8) (.zero 1)))))))))

/-- The nine source registers at a scheduler command boundary. -/
noncomputable def frame : Code 1 :=
  PA194SourceControllerCode.state 25
    (fileCode ![fN,fT,fW,.zero 1,fD,fH,.zero 1,.zero 1,fL])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def arguments (s : M) : Fin 11 → M :=
  ![F fN ![s],F fT ![s],F fW ![s],0,F fD ![s],F fH ![s],0,0,F fL ![s],0,0]

theorem frame_model (s : M) : F frame ![s] = sourceState 25 (arguments s) (0 : M) := by
  rw [frame,PA194SourceInstructionModel.stateModel]
  simp [fileCode,modelBin,modelPairCode,PRAMultiplication.modelZero,
    sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,arguments] <;> rfl

theorem frame_pc (s : M) : F pc ![F frame ![s]] = modelNumeral M 25 := by
  rw [frame_model]
  exact PA194SourceFetchLoop.statePC 25 (arguments s) 0

theorem frame_initial : F frame ![F initial Fin.elim0] = (initialSource : M) := by
  have htwo : modelNumeral M 2 = (2 : M) := by
    rw [show modelNumeral M 2 = modelNumeral M 1 + 1 from PA194FiniteControls.modelNumeralSucc 1,
      PA194StateOne.modelNumeralOne]
    exact one_add_one_eq_two
  have hregs : regsOfArgs (arguments (F initial Fin.elim0)) =
      regsOfArgs (startArgs (M := M)) := by
    funext i
    fin_cases i <;>
      simp [regsOfArgs,arguments,startArgs,seedArgs,initial,fN,fL,fT,fW,fD,fH,
        fst_model,snd_model,pack_model,modelProjection,PA194NumeralCode.modelNumeralCode,
        pi₁_pair,pi₂_pair,htwo] <;> rfl
  rw [frame_model]
  change sourceState 25 (arguments (F initial Fin.elim0)) 0 = sourceState 25 startArgs 0
  simp only [sourceState,hregs]

theorem haltFromFrame (s : M) (h : F haltAt ![s] = (1 : M)) :
    ∃ c : M, F pc ![F PA194SourceControllerCode.run ![c,F frame ![s]]] =
      modelNumeral M 3674 := by
  rw [frame_model]
  exact PA194SchedulerHaltSource.haltFromRoot s (arguments s) 0 rfl rfl rfl rfl rfl rfl rfl h

/-- The returning-command contract suffices for the global correspondence;
the halting-command contract follows from the verified literal SHIFT path. -/
theorem equivalent_of_return
    (returning : ∀ s : M, F haltAt ![s] ≠ 1 →
      ∃ c : M, 0 < c ∧ F PA194SourceControllerCode.run ![c,F frame ![s]] =
        F frame ![F PA194SchedulerIteration.step ![s]]) :
    (∃ t : M, F pc ![F PA194SourceControllerCode.run ![t,initialSource]] =
      modelNumeral M 3674) ↔
    (∃ n : M, F haltAt ![F PA194SchedulerIteration.run ![n,F initial Fin.elim0]] = 1) := by
  exact PA194SourceSchedulerOrbit.equivalent PA194SchedulerIteration.step haltAt
    frame (F initial Fin.elim0) initialSource frame_initial.symm frame_pc returning haltFromFrame

#print axioms frame_model
#print axioms frame_initial
#print axioms haltFromFrame
#print axioms equivalent_of_return
end models
end PA194SchedulerSourceFrame
