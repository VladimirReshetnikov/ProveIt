import PA194M5DecodeScheduler
import PA194M5MPFields
import PA194M5MPDispatch
import PA194SchedulerSourceFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5MPFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SchedulerCode PA194SchedulerIteration
open PA194ModelMPDrain PA194TargetCantor PA194MachineProjections PA194ModelMPImp
open PA194SchedulerSourceFrame PA194SourceRegisterRelation PA194IteratedSimulation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

theorem advance (s ns : M) (hMP : F (head fN fL) ![s] = 1)
    (hn : F fN ![ns] = F (nextN fN fL) ![s])
    (hl : F fL ![ns] = F fixedSecond ![F (PA194SchedulerCode.tail fN fL) ![s]])
    (ht : F fT ![ns] = (if PA194ProgramCons.implicationValue 5 (F fT ![s]) (F fD ![s] + F fixedFirst ![F (PA194SchedulerCode.tail fN fL) ![s]]) = F fH ![s]
      then F fD ![s] + F fixedFirst ![F (PA194SchedulerCode.tail fN fL) ![s]] else 0))
    (hw : F fW ![ns] = (if PA194ProgramCons.implicationValue 5 (F fT ![s]) (F fD ![s] + F fixedFirst ![F (PA194SchedulerCode.tail fN fL) ![s]]) = F fH ![s]
      then cantor 0 (F fW ![s]) else F fW ![s]))
    (hd : F fD ![ns] = F fD ![s] + F fixedFirst ![F (PA194SchedulerCode.tail fN fL) ![s]])
    (hh : F fH ![ns] = 0) :
    ∃ n : M, 0 < n ∧ F (iterate (PA194ProgramDrain.step PA194M5Program.program)) ![n,F frame ![s]] = F frame ![ns] := by
  let a := arguments s
  have h0 : F fN ![s] = a 0 := by rfl
  have h8 : F fL ![s] = a 8 := by rfl
  have h6 : a 6 = 0 := by rfl
  have h7 : a 7 = 0 := by rfl
  have h3 : a 3 = 0 := by rfl
  obtain ⟨out,reach,hout3,hout8,hout0,hout6,hout7,other⟩ :=
    PA194M5DecodeScheduler.fetchDecode s a 0 h0 h8 h6 h7 h3
  have hop : out 3 = 1 := hout3.symm.trans hMP
  let b := Function.update out 3 0
  have db : PA194ProgramDrain.Reaches PA194M5Program.program (sourceState 25 a 0) (sourceState 48 out 0) := reach
  have dmp := PA194M5MPDispatch.mp out 0 hop
  have bx : b 6 = (0 : M) := by simp [b,hout6]
  have by' : b 7 = (0 : M) := by simp [b,hout7]
  have command := PA194M5MPCommand.command b 0 bx by'
  obtain ⟨n,hpos,hrun⟩ := PA194ProgramDrain.appendPositive PA194M5Program.program
    (PA194ProgramDrain.append PA194M5Program.program db dmp) command
  let res := PA194M5MPCommand.result b
  have hv := PA194M5MPFields.resultFields b
  dsimp only at hv
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,v8⟩ := hv
  have o1 : out 1 = F fT ![s] := by simpa [a,arguments] using other 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have o2 : out 2 = F fW ![s] := by simpa [a,arguments] using other 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have o4 : out 4 = F fD ![s] := by simpa [a,arguments] using other 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have o5 : out 5 = F fH ![s] := by simpa [a,arguments] using other 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hre : regsOfArgs res = regsOfArgs (arguments ns) := by
    funext i
    fin_cases i <;> simp [regsOfArgs,arguments,res,b,v0,v1,v2,v3,v4,v5,v6,v7,v8,
      hout0,hout8,hout6,hout7,o1,o2,o4,o5,hn,hl,ht,hw,hd,hh]
  have htarget : sourceState 25 res (0:M) = F frame ![ns] := by
    rw [frame_model]
    simp only [sourceState,hre]
  rw [frame_model]
  exact ⟨n,hpos,hrun.trans htarget⟩
#print axioms advance
end models
end PA194M5MPFrame
