import PA194SchedulerSourceFrame
import PA194AX11HAXSchedulerFields
import PA194AX11HBodyToFrame
import PA194AX11HDecodeScheduler
import PA194AX11HAXDispatch
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HAXFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194SchedulerIteration PA194SchedulerCode PA194MachineShiftMPCode PA194MachineProjections
open PA194SchedulerSourceFrame PA194AX11HBodyCopy PA194AXModelValues PA194MachineStack
open PA194ControllerScheduler PA194PathIterator
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

private theorem unaryValue (f g : Code 1) (s : M) : F (unary f g) ![s] = F f ![F g ![s]] := by
  rw [PA194PathIterator.modelUnary]
  apply congrArg (F f)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

/-- Exact AX source-command contract for the concrete AX11H scheduler, conditional
only on candidate/primary body-row agreement. -/
theorem advance (agree : BodyRowsAgree) (s c : M)
    (htag : F (head fN fL) ![s] = (c+1)+1) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,F frame ![s]] =
      F frame ![F (stepK .top true) ![s]] := by
  let init := arguments s
  let ns := F (stepK .top true) ![s]
  have h0 : F fN ![s] = init 0 := by rfl
  have h8 : F fL ![s] = init 8 := by rfl
  have h6 : init 6 = 0 := by rfl
  have h7 : init 7 = 0 := by rfl
  have h3 : init 3 = 0 := by rfl
  obtain ⟨out,hfetch,hhead,htail,hnext,hx,hy,hkeep⟩ :=
    PA194AX11HDecodeScheduler.fetchDecode s init 0 h0 h8 h6 h7 h3
  have hop : out 3 = (c+1)+1 := hhead.symm.trans htag
  let a := Function.update out 3 c
  have hdispatch := PA194AX11HAXDispatch.dispatch out 0 c hop
  have ax : a 6 = 0 := (Function.update_of_ne (by decide) c out).trans hx
  have ay : a 7 = 0 := (Function.update_of_ne (by decide) c out).trans hy
  obtain ⟨t,ht,hrun⟩ := PA194AX11HBodyToFrame.body_to_frame agree a 0 ax ay
  let b := bodyValues a
  let result : Fin 11 → M := ![b 0,0,cantor (axTop (b 5) (b 4) (b 3)) (b 2),0,
    F fixedFirst ![b 8],0,0,0,F fixedSecond ![b 8],0,0]
  change F (iterate PA194AX11HSource.step) ![t,sourceState 50 a 0] = sourceState 25 result 0 at hrun
  have a0 : a 0 = F (nextN fN fL) ![s] := (Function.update_of_ne (by decide) c out).trans hnext.symm
  have a1 : a 1 = F fT ![s] := by simpa [a,init,arguments] using hkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have a2 : a 2 = F fW ![s] := by simpa [a,init,arguments] using hkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have a3 : a 3 = c := Function.update_self 3 c out
  have a4 : a 4 = F fD ![s] := by simpa [a,init,arguments] using hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have a5 : a 5 = F fH ![s] := by simpa [a,init,arguments] using hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have a8 : a 8 = F (PA194SchedulerCode.tail fN fL) ![s] := (Function.update_of_ne (by decide) c out).trans htail.symm
  obtain ⟨nN,nL,nT,nW,nD,nH⟩ := PA194AX11HAXSchedulerFields.nextFields s c htag
  have hre : regsOfArgs result = regsOfArgs (arguments ns) := by
    funext i
    fin_cases i <;> simp [regsOfArgs,arguments,result,b,bodyValues,a0,a1,a2,a3,a4,a5,a8,
      ns,nN,nL,nT,nW,nD,nH,yArg,xArg,tail2,tail3,zArg,tail4,unaryValue]
  have hframe : sourceState 25 result (0 : M) = F frame ![ns] := by
    rw [frame_model]
    simp only [sourceState,hre]
  obtain ⟨u,hu⟩ := PA194PausedReach.append _ hfetch hdispatch
  refine ⟨u+t,lt_of_lt_of_le ht ?_,?_⟩
  · simpa [zero_add] using add_le_add (zero_le : (0 : M) ≤ u) (le_refl t)
  · rw [frame_model,PA194ControllerRunAdd.iterateAdd,hu,hrun,hframe]
#print axioms advance
end models
end PA194AX11HAXFrame
