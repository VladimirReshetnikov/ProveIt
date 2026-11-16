import PA194ModelAXBound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194ModelAXBody
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelAXPlan PA194ModelAXPlanPositive PA194ModelAXBound PA194AXSymbolic
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

theorem execute (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive (sourceState 50 a tail) (sourceState 3519 (actions core a) tail) := by
  have hplan : Plan 50 3519 (.push :: [.copyH, .push, .copyD, .cons, .incT, .incT, .readH, .push, .copyH, .push, .copyD, .cons, .readD, .push, .copyD, .cons, .push, .copyD, .push, .copyH, .cons, .push, .copyA, .push, .copyH, .cons, .cons, .cons, .push, .copyH, .push, .copyD, .cons, .incT, .incT, .push, .incT, .cons, .push, .copyD, .cons, .incT, .incT, .push, .incT, .cons, .push, .copyH, .cons, .push, .copyH, .push, .copyA, .cons, .incT, .incT, .push, .copyD, .cons, .incT, .incT, .push, .copyH, .push, .copyD, .cons, .incT, .incT, .push, .copyA, .cons, .incT, .incT, .cons, .push, .copyH, .push, .copyD, .cons, .incT, .push, .copyH, .push, .copyA, .cons, .incT, .incT, .incT, .push, .copyA, .push, .copyD, .cons, .incT, .cons, .cons, .push, .copyH, .push, .copyD, .cons, .incT, .incT, .incT, .push, .copyA, .push, .copyH, .cons, .incT, .push, .copyA, .push, .copyD, .cons, .incT, .cons, .cons, .push, .copyH, .push, .copyD, .cons, .incT, .incT, .incT, .push, .incT, .cons, .push, .copyD, .cons, .incT, .incT, .push, .incT, .cons, .push, .copyA, .push, .copyD, .cons, .incT, .incT, .push, .copyA, .push, .copyH, .cons, .push, .copyD, .cons, .incT, .incT, .push, .copyH, .push, .copyD, .cons, .incT, .incT, .cons, .cons, .push, .copyA, .push, .copyA, .push, .copyA, .cons, .incT, .incT, .cons, .push, .copyH, .push, .copyD, .cons, .incT, .push, .copyH, .push, .copyD, .cons, .incT, .push, .copyA, .cons, .incT, .incT, .cons, .push, .copyH, .push, .copyD, .cons, .incT, .push, .copyA, .push, .copyA, .push, .copyD, .cons, .incT, .cons, .cons, .push, .copyA, .push, .copyD, .cons, .incT, .push, .copyA, .cons, .push, .incT, .cons, .cons, .push, .incT, .cons, .push, .copyD, .cons, .incT, .incT, .push, .copyA, .push, .copyA, .push, .copyD, .cons, .incT, .cons, .push, .incT, .cons, .cons, .push, .copyA, .cons, .incT, .incT, .cons, .push, .incT, .cons]) := by exact sourcePlan
  have h := executePositive hplan a tail hx hy
  exact h
#print axioms execute
end models
end PA194ModelAXBody
