import PA194ModelAXPlan
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194ModelAXPlanPositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelAXPlan
open M6.Source.AXMacro
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

theorem appendFirst {s t u : M} (h : ReachesPositive s t) (h' : Reaches t u) : ReachesPositive s u := by
  obtain ⟨c,hc,he⟩ := h
  obtain ⟨d,hd⟩ := h'
  have hd' : (0 : M) ≤ d := zero_le
  refine ⟨c+d,lt_of_lt_of_le hc (le_add_of_nonneg_right hd'),?_⟩
  change F (PA194IteratedSimulation.iterate step) ![c+d,s] = u
  rw [PA194ControllerRunAdd.iterateAdd]
  change F run ![d,F run ![c,s]] = u
  rw [he,hd]

theorem executePositive {base exit : Nat} {op : Op} {ops : List Op}
    (plan : Plan base exit (op::ops)) (a : Fin 11 → M) (tail : M)
    (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive (sourceState base a tail) (sourceState exit (actions (op::ops) a) tail) := by
  cases plan with
  | cons rows rest =>
    have h := executeOne rows a tail hx hy
    have hg := actionGood op a hx hy
    exact appendFirst h (executePlan rest (action op a) tail hg.1 hg.2)

#print axioms appendFirst
#print axioms executePositive
end models
end PA194ModelAXPlanPositive
