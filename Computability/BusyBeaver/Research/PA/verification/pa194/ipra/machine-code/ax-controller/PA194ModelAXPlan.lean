import M6.Source.AXMacro
import PA194ModelAXConsExecute
import PA194ModelAXReads
import PA194ModelAXCopy
import PA194ModelMPPush
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelAXPlan
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation PA194SourceFetchLoop PA194ModelMPDrain PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.Source.AXMacro

inductive Bound : Nat → Nat → Op → Prop where
  | push (base) : PA194ModelMPPush.Rows base → Bound base (base+19) .push
  | copyA (base) : PA194ModelAXCopy.Rows base 3 → Bound base (base+7) .copyA
  | copyD (base) : PA194ModelAXCopy.Rows base 4 → Bound base (base+7) .copyD
  | copyH (base) : PA194ModelAXCopy.Rows base 5 → Bound base (base+7) .copyH
  | cons (base) : PA194ModelAXCons.Rows base → Bound base (base+27) .cons
  | incT (base) : base < 3673 → row base = some (.inc 1 (some (base+1))) → Bound base (base+1) .incT
  | readH (base) : PA194ModelAXReader.ReaderRows base 8 5 → Bound base (base+14) .readH
  | readD (base) : PA194ModelAXReader.ReaderRows base 8 4 → Bound base (base+14) .readD

inductive Plan : Nat → Nat → List Op → Prop where
  | nil (base) : Plan base base []
  | cons {base middle exit op ops} : Bound base middle op → Plan middle exit ops →
      Plan base exit (op::ops)

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

noncomputable def action (op : Op) (a : Fin 11 → M) : Fin 11 → M :=
  match op with
  | .push => PA194ModelMPPush.pushed a
  | .copyA => Function.update a 1 (a 1+a 3)
  | .copyD => Function.update a 1 (a 1+a 4)
  | .copyH => Function.update a 1 (a 1+a 5)
  | .incT => Function.update a 1 (a 1+1)
  | .cons => Function.update (Function.update (Function.update (Function.update a
      1 (modelNumeral M 4 * cantor (F fixedFirst ![a 2]) (a 1)))
      2 (F fixedSecond ![a 2])) 6 0) 7 0
  | .readH => Function.update (Function.update (Function.update (Function.update a
      8 (F fixedSecond ![a 8])) 5 (a 5+F fixedFirst ![a 8])) 6 0) 7 0
  | .readD => Function.update (Function.update (Function.update (Function.update a
      8 (F fixedSecond ![a 8])) 4 (a 4+F fixedFirst ![a 8])) 6 0) 7 0

theorem actionGood (op : Op) (a : Fin 11 → M) (hx : a 6 = 0) (hy : a 7 = 0) :
    action op a 6 = 0 ∧ action op a 7 = 0 := by
  cases op <;> simp [action, PA194ModelMPPush.pushed, hx,hy]

theorem executeOne {base exit : Nat} {op : Op} (rows : Bound base exit op)
    (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive (sourceState base a tail) (sourceState exit (action op a) tail) := by
  cases rows with
  | push h => exact PA194ModelMPPush.push base h a tail hx hy
  | copyA h => exact PA194ModelAXCopy.copy base 3 h a tail hx
  | copyD h => exact PA194ModelAXCopy.copy base 4 h a tail hx
  | copyH h => exact PA194ModelAXCopy.copy base 5 h a tail hx
  | cons h => exact PA194ModelAXConsExecute.execute base h a tail hx hy
  | incT hv h =>
    apply oneStep
    exact sourceInc base (base+1) 1 hv h a tail
  | readH h => exact PA194ModelAXReads.readH base h a tail hx hy
  | readD h => exact PA194ModelAXReads.readD base h a tail hx hy

noncomputable def actions : List Op → (Fin 11 → M) → (Fin 11 → M)
  | [], a => a
  | op::ops, a => actions ops (action op a)

theorem executePlan {base exit : Nat} {ops : List Op} (plan : Plan base exit ops)
    (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    Reaches (sourceState base a tail) (sourceState exit (actions ops a) tail) := by
  induction plan generalizing a with
  | nil base =>
    refine ⟨0,?_⟩
    exact PA194IteratedSimulation.iterateZero step _
  | @cons b m e op ops rows rest ih =>
    have h := executeOne rows a tail hx hy
    have good := actionGood op a hx hy
    exact append h.reaches (ih (action op a) good.1 good.2)

#print axioms executeOne
#print axioms executePlan
end models
end PA194ModelAXPlan
