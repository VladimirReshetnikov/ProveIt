import PA194ModelAXBound
import PA194PausedReach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HPlanReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194ModelAXPlan PA194ModelAXBound PA194AXSymbolic M6.Source.AXMacro

theorem bound_le {base exit : Nat} {op : Op} (h : Bound base exit op) : base ≤ exit := by
  cases h <;> omega

theorem plan_le {base exit : Nat} {ops : List Op} (p : Plan base exit ops) : base ≤ exit := by
  induction p with
  | nil => exact le_rfl
  | cons h _ ih => exact le_trans (bound_le h) ih

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

/-- A candidate source execution for each certified primary AX macro in the body window. -/
def MacroSupply (step : Code 1) : Prop :=
  ∀ (base exit : Nat) (op : Op), Bound base exit op → 50 ≤ base → exit ≤ 3519 →
    ∀ (a : Fin 11 → M) (tail : M), a 6 = 0 → a 7 = 0 →
      PA194PausedReach.Reaches step (sourceState base a tail) (sourceState exit (action op a) tail)

theorem executePlan (step : Code 1) (supply : MacroSupply (M := M) step)
    {base exit : Nat} {ops : List Op} (p : Plan base exit ops)
    (hbase : 50 ≤ base) (hexit : exit ≤ 3519)
    (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches step (sourceState base a tail) (sourceState exit (actions ops a) tail) := by
  induction p generalizing a with
  | nil base =>
    refine ⟨0,?_⟩
    exact iterateZero step _
  | @cons base middle exit op ops rows rest ih =>
    have hmiddle : middle ≤ exit := plan_le rest
    have hfirst := supply base middle op rows hbase (le_trans hmiddle hexit) a tail hx hy
    have hgood := actionGood op a hx hy
    have hrest := ih (le_trans hbase (bound_le rows)) hexit (action op a) hgood.1 hgood.2
    exact PA194PausedReach.append step hfirst hrest

/-- Once the eight model-uniform macro cases are supplied, the existing 251-operation
primary plan gives the exact source body for the candidate step. -/
theorem body (step : Code 1) (supply : MacroSupply (M := M) step)
    (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches step (sourceState 50 a tail) (sourceState 3519 (actions core a) tail) :=
  executePlan step supply sourcePlan (by decide) (by decide) a tail hx hy
#print axioms body
end models
end PA194AX11HPlanReduction
