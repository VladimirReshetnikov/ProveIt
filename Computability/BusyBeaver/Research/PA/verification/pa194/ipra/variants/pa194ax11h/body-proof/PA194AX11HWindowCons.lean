import PA194AX11HWindowWalkerLoop
import PA194AX11HWindowPair
import PA194AX11HWindowTransfer
import PA194ModelAXCons
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194WindowCons
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelCantorWalker PA194ModelMPTransfer PA194MachineProjections PA194WindowDrain PA194ModelAXCons
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

/-- Exact 27-row constructor, with the final registers expressed by the
    generic drain operation. The fourfold tally encodes implication tagging. -/
theorem cons (codeStep : Code 1) (lower bound base : Nat) (hagrees : AgreesWindow (M := M) codeStep lower bound) (hbase : lower ≤ base) (hbelow : base+26 < bound) (rows : Rows base) (a : Fin 11 → M) (tail : M) :
    let code := cantor (a 6) (a 7) + a 2
    let popped := argsAt 2 a (F fixedFirst ![code]) (F fixedSecond ![code]) 0
    let restored := transferArgs popped 7 2
    let packed := PA194ModelMPPair.values restored 0 0 (cantor (restored 6) (restored 1))
    let out := argsAfter packed 7 [1,1,1,1] (packed 7)
    PA194PausedReach.Reaches codeStep (sourceState base a tail) (sourceState (base+27) out tail) := by
  dsimp only
  let code := cantor (a 6) (a 7) + a 2
  let popped := argsAt 2 a (F fixedFirst ![code]) (F fixedSecond ![code]) 0
  let restored := transferArgs popped 7 2
  let packed := PA194ModelMPPair.values restored 0 0 (cantor (restored 6) (restored 1))
  have hpop := PA194WindowWalkerLoop.walk codeStep lower bound base hagrees hbase (by omega) 2 rows.pop (by decide) (by decide) a tail
  change PA194PausedReach.Reaches codeStep (sourceState base a tail) (sourceState (base+8) popped tail) at hpop
  have hrestore := PA194WindowTransfer.transfer codeStep lower bound (base+8) (base+11) 7 2 hagrees rows.restore (by omega) (by omega) (by decide) popped tail
  change PA194PausedReach.Reaches codeStep (sourceState (base+8) popped tail) (sourceState (base+11) restored tail) at hrestore
  have hY : restored 7 = (0 : M) := by simp [restored,transferArgs,location]
  have hpair := PA194WindowPair.pair codeStep lower bound (base+11) hagrees (by omega) (by omega) rows.pair restored tail hY
  change PA194PausedReach.Reaches codeStep (sourceState (base+11) restored tail) (sourceState (base+21) packed tail) at hpair
  have path : SafeIncrements lower bound (base+21) (base+22) [1,1,1,1] :=
    .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.four1
      (.inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.four2
        (.inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.four3
          (.inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.four4
            (.jump _ rows.valid (by omega) (by omega) rows.fourBack))))
  have hfour := PA194WindowDrain.drain codeStep lower bound hagrees (base+21) (base+22) (base+27) 7 [1,1,1,1]
    (by have := rows.valid; omega) (by omega) (by omega) rows.fourTest path (by decide) packed tail
  exact PA194PausedReach.append codeStep (PA194PausedReach.append codeStep (PA194PausedReach.append codeStep hpop hrestore) hpair) hfour

#print axioms cons
end models
end PA194WindowCons
