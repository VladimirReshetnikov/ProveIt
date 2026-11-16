import PA194AX11HPlanReduction
import PA194AX11HBodyWindow
import PA194AX11HWindowPush
import PA194AX11HWindowReads
import PA194AX11HWindowConsExecute
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HBodyAll
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194ModelAXPlan PA194ModelAXBound PA194AXSymbolic M6.Source.AXMacro
open PA194AX11HPlanReduction PA194AX11HBodyCopy
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

theorem macroSupply (agree : BodyRowsAgree) :
    MacroSupply (M := M) PA194AX11HSource.step := by
  intro base exit op rows hbase hexit a tail hx hy
  have ha := PA194AX11HBodyWindow.body_window (M := M) agree
  cases rows with
  | push rows =>
    rename_i base
    simpa only [action] using PA194WindowPush.push PA194AX11HSource.step 50 3519 base ha hbase (by omega) rows a tail hx hy
  | copyA rows =>
    rename_i base
    simpa only [action,show PA194ModelMPDrain.location (3 : Fin 9) = (3 : Fin 11) by decide] using PA194AX11HBodyCopy.copy agree base 3 rows hbase hexit a tail hx
  | copyD rows =>
    rename_i base
    simpa only [action,show PA194ModelMPDrain.location (4 : Fin 9) = (4 : Fin 11) by decide] using PA194AX11HBodyCopy.copy agree base 4 rows hbase hexit a tail hx
  | copyH rows =>
    rename_i base
    simpa only [action,show PA194ModelMPDrain.location (5 : Fin 9) = (5 : Fin 11) by decide] using PA194AX11HBodyCopy.copy agree base 5 rows hbase hexit a tail hx
  | incT valid row =>
    rename_i base
    have cr := (agree base hbase (by omega)).trans row
    have h := PA194AX11HSourceAt.sourceInc base (base+1) 1 (by omega) cr a tail
    change F PA194AX11HSource.step ![sourceState base a tail] =
      sourceState (base+1) (Function.update a 1 (a 1+1)) tail at h
    exact PA194PausedReach.oneStep _ h
  | cons rows =>
    rename_i base
    simpa only [action] using PA194WindowConsExecute.execute PA194AX11HSource.step 50 3519 base ha hbase (by omega) rows a tail hx hy
  | readH rows =>
    rename_i base
    simpa only [action] using PA194WindowReads.readH PA194AX11HSource.step 50 3519 base ha hbase (by omega) rows a tail hx hy
  | readD rows =>
    rename_i base
    simpa only [action] using PA194WindowReads.readD PA194AX11HSource.step 50 3519 base ha hbase (by omega) rows a tail hx hy

theorem body (agree : BodyRowsAgree)
    (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 50 a tail) (sourceState 3519 (actions core a) tail) :=
  PA194AX11HPlanReduction.body _ (macroSupply agree) a tail hx hy
#print axioms body
end models
end PA194AX11HBodyAll
