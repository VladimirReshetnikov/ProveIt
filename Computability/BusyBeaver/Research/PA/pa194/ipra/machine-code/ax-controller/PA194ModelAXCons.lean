import PA194ModelCantorWalker
import PA194ModelMPTransfer
import PA194ModelMPPair
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelAXCons
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelCantorWalker PA194ModelMPTransfer PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

structure Rows (base : Nat) : Prop where
  valid : base+26 < 3673
  pop : PA194ModelCantorWalker.Rows base 2
  restore : TransferRows (base+8) (base+11) 7 2
  pair : PA194ModelMPPair.Rows (base+11)
  fourTest : row (base+21) = some (.dec 7 (some (base+27)) (some (base+22)))
  four1 : row (base+22) = some (.inc 1 (some (base+23)))
  four2 : row (base+23) = some (.inc 1 (some (base+24)))
  four3 : row (base+24) = some (.inc 1 (some (base+25)))
  four4 : row (base+25) = some (.inc 1 (some (base+26)))
  fourBack : row (base+26) = some (.jump (some (base+21)))

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
theorem cons (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail : M) :
    let code := cantor (a 6) (a 7) + a 2
    let popped := argsAt 2 a (F fixedFirst ![code]) (F fixedSecond ![code]) 0
    let restored := transferArgs popped 7 2
    let packed := PA194ModelMPPair.values restored 0 0 (cantor (restored 6) (restored 1))
    let out := argsAfter packed 7 [1,1,1,1] (packed 7)
    ReachesPositive (sourceState base a tail) (sourceState (base+27) out tail) := by
  dsimp only
  let code := cantor (a 6) (a 7) + a 2
  let popped := argsAt 2 a (F fixedFirst ![code]) (F fixedSecond ![code]) 0
  let restored := transferArgs popped 7 2
  let packed := PA194ModelMPPair.values restored 0 0 (cantor (restored 6) (restored 1))
  have hpop := walk base 2 rows.pop (by decide) (by decide) a tail
  change ReachesPositive (sourceState base a tail) (sourceState (base+8) popped tail) at hpop
  have hrestore := transfer (base+8) (base+11) 7 2 rows.restore (by decide) popped tail
  change ReachesPositive (sourceState (base+8) popped tail) (sourceState (base+11) restored tail) at hrestore
  have hY : restored 7 = (0 : M) := by simp [restored,transferArgs,location]
  have hpair := PA194ModelMPPair.pair (base+11) rows.pair restored tail hY
  change ReachesPositive (sourceState (base+11) restored tail) (sourceState (base+21) packed tail) at hpair
  have path : Increments (base+21) (base+22) [1,1,1,1] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.four1
      (.inc _ _ _ _ (by have := rows.valid; omega) rows.four2
        (.inc _ _ _ _ (by have := rows.valid; omega) rows.four3
          (.inc _ _ _ _ (by have := rows.valid; omega) rows.four4
            (.jump _ rows.valid rows.fourBack))))
  have hfour := drain (base+21) (base+22) (base+27) 7 [1,1,1,1]
    (by have := rows.valid; omega) rows.fourTest path (by decide) packed tail
  exact appendPositive (append (append hpop.reaches hrestore.reaches) hpair.reaches) hfour

#print axioms cons
end models
end PA194ModelAXCons
