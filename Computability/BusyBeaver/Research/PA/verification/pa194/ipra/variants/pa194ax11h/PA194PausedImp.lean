import PA194PausedWalkerLoop
import PA194PausedPair
import PA194PausedTransfer
import PA194ModelMPImp
import PA194ModelMPPair
import PA194ModelMPTransfer
import PA194MPLiteralRows3594

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194PausedImp
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelMPTransfer PA194MPLiteralRows PA194ModelMPImp PA194PausedDrain
open PA194MachineProjections PA194TargetCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pop (code : Code 1) (bound : Nat) (hagrees : AgreesBelow (M := M) code bound)
    (hbelow : 3620 < bound) (a : Fin 11 → M) (tail h w : M) (hX : a 6 = 0) (hY : a 7 = 0)
    (hW : a 2 = cantor h w) :
    PA194PausedReach.Reaches code (sourceState 3594 a tail) (sourceState 3605 (popped a h w) tail) := by
  have hp := PA194PausedWalkerLoop.walk code bound 3594 hagrees (by omega) 2 popRows (by decide) (by decide) a tail
  have hz : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  change PA194PausedReach.Reaches code (sourceState 3594 a tail) (sourceState 3602
    (PA194ModelCantorWalker.argsAt 2 a (F fixedFirst ![cantor (a 6) (a 7)+a 2])
      (F fixedSecond ![cantor (a 6) (a 7)+a 2]) 0) tail) at hp
  rw [hX,hY,hz,zero_add,hW,fixedFirst_model,first_cantor,fixedSecond_model,second_cantor] at hp
  let b := PA194ModelCantorWalker.argsAt 2 a h w 0
  have rows : TransferRows 3602 3605 7 2 := ⟨by decide,s3602,s3603,s3604⟩
  have hr := PA194PausedTransfer.transfer code bound 3602 3605 7 2 hagrees rows (by omega) (by decide) b tail
  have he : transferArgs b 7 2 = popped a h w := by
    funext i
    fin_cases i <;> simp [b,PA194ModelCantorWalker.argsAt,PA194ModelCantorWalker.write,
      transferArgs,location,popped,hY]
  rw [he] at hr
  exact PA194PausedReach.append code hp hr

theorem build (code : Code 1) (bound : Nat) (hagrees : AgreesBelow (M := M) code bound)
    (hbelow : 3620 < bound) (a : Fin 11 → M) (tail h w : M) (hX : a 6 = 0) (hY : a 7 = 0)
    (hW : a 2 = cantor h w) :
    PA194PausedReach.Reaches code (sourceState 3594 a tail)
      (sourceState 3621 (implicationArgs a (impValue h (a 1)) w) tail) := by
  let b := popped a h w
  let c := PA194ModelMPPair.values b 0 0 (cantor (b 6) (b 1))
  have hp := pop code bound hagrees hbelow a tail h w hX hY hW
  have hyb : b 7 = (0 : M) := by simp [b,popped,hY]
  have hpair := PA194PausedPair.pair code bound 3605 hagrees (by omega) pairRows b tail hyb
  have path : SafeIncrements bound 3615 3616 [1,1,1,1] :=
    .inc 3616 3617 1 _ (by decide) (by omega) s3616
      (.inc 3617 3618 1 _ (by decide) (by omega) s3617
        (.inc 3618 3619 1 _ (by decide) (by omega) s3618
          (.inc 3619 3620 1 _ (by decide) (by omega) s3619 (.jump 3620 (by decide) (by omega) s3620))))
  have hmul := PA194PausedDrain.drain code bound hagrees 3615 3616 3621 7 [1,1,1,1] (by decide) (by omega) s3615 path (by decide) c tail
  have h4 : modelNumeral M 4 = (4 : M) := by
    rw [show (4 : Nat) = 1+1+1+1 by decide,
      PA194FiniteControls.modelNumeralAdd,PA194FiniteControls.modelNumeralAdd,
      PA194FiniteControls.modelNumeralAdd,PA194StateOne.modelNumeralOne]
    norm_num
  have he : argsAfter c 7 [1,1,1,1] (c (location 7)) =
      implicationArgs a (impValue h (a 1)) w := by
    funext i
    fin_cases i <;> simp [argsAfter,tally,c,b,popped,PA194ModelMPPair.values,location,
      implicationArgs,hX,hY,impValue,h4,subSelf,show modelNumeral M 0 = (0:M) from rfl]
  rw [he] at hmul
  exact PA194PausedReach.append code (PA194PausedReach.append code hp hpair) hmul

#print axioms pop
#print axioms build
end models
end PA194PausedImp
