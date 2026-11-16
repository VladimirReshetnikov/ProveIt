import PA194PausedCopy
import PA194PausedImp
import PA194PausedTransfer
import PA194PausedFirstHit
import PA194AX11HPrepPaused
import PA194ModelMPGuard
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194PausedPrep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SourceControllerBinding PA194SourcePCBound PA194StateOne PA194FiniteControls
open PA194SchedulerFetchPositive PA194SourceFetchLoop PA194IteratedSimulation
open PA194ModelMPDrain PA194ModelMPCopy PA194ModelMPImp PA194ModelMPTransfer PA194MPLiteralRows PA194TargetCantor
open PA194PausedDrain PA194PausedTransfer
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

theorem prep_agrees : AgreesBelow (M := M) PA194AX11HPrepPaused.oldPaused 3624 := by
  intro site hs a tail
  rw [PA194AX11HPrepPaused.oldPaused_model,statePC]
  have hn : modelNumeral M site ≠ modelNumeral M 3624 :=
    ne_of_lt (modelNumeralStrict site 3624 hs)
  rw [if_neg hn]

noncomputable def result (a : Fin 11 → M) (h w : M) : Fin 11 → M :=
  let d := Function.update a 1 (a 1+a 4)
  let i := implicationArgs d (impValue h (d 1)) w
  transferArgs i 1 6

/-- Frozen primary preparation: D-copy, implication construction, and guard setup. -/
theorem paused_prep (a : Fin 11 → M) (tail h w : M)
    (hx : a 6 = 0) (hy : a 7 = 0) (hw : a 2 = cantor h w) :
    PA194PausedReach.Reaches PA194AX11HPrepPaused.oldPaused
      (sourceState 3587 a tail) (sourceState 3624 (result a h w) tail) := by
  let d := Function.update a 1 (a 1+a 4)
  let i := implicationArgs d (impValue h (d 1)) w
  have hc := PA194PausedCopy.copy PA194AX11HPrepPaused.oldPaused 3624 3587 prep_agrees (by decide)
    PA194ModelMPCopy.entryRows a tail hx
  have hd6 : d 6 = (0 : M) := by simp [d,hx]
  have hd7 : d 7 = (0 : M) := by simp [d,hy]
  have hd2 : d 2 = cantor h w := by simp [d,hw]
  have hi := PA194PausedImp.build PA194AX11HPrepPaused.oldPaused 3624 prep_agrees (by decide)
    d tail h w hd6 hd7 hd2
  have rows : TransferRows 3621 3624 1 6 := ⟨by decide,s3621,s3622,s3623⟩
  have ht := PA194PausedTransfer.transfer PA194AX11HPrepPaused.oldPaused 3624 3621 3624 1 6
    prep_agrees rows (by decide) (by decide) i tail
  change PA194PausedReach.Reaches _ (sourceState 3587 a tail) (sourceState 3594 d tail) at hc
  change PA194PausedReach.Reaches _ (sourceState 3594 d tail) (sourceState 3621 i tail) at hi
  change PA194PausedReach.Reaches _ (sourceState 3621 i tail) (sourceState 3624 (result a h w) tail) at ht
  exact PA194PausedReach.append _ (PA194PausedReach.append _ hc hi) ht

theorem first_actual_prep (a : Fin 11 → M) (tail h w : M)
    (hx : a 6 = 0) (hy : a 7 = 0) (hw : a 2 = cantor h w) :
    ∃ n : M, F (iterate step) ![n,sourceState 3587 a tail] = sourceState 3624 (result a h w) tail ∧
      ∀ j < n, F pc ![F (iterate step) ![j,sourceState 3587 a tail]] ≠ modelNumeral M 3624 := by
  apply PA194PausedFirstHit.first_actual_exit PA194AX11HPrepPaused.oldPaused 3624
  · exact PA194AX11HPrepPaused.oldPaused_model
  · exact statePC 3624 (result a h w) tail
  · exact paused_prep a tail h w hx hy hw

#print axioms prep_agrees
#print axioms paused_prep
#print axioms first_actual_prep
end models
end PA194PausedPrep
