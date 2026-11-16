import PA194HXControllerHalt
import PA194HXSeedFrame
import PA194CompressedStartup
import PA194VariantController

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194HXSourceEndpoint
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194CompressedStartup PA194Path27Header

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem numeralCast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [modelNumeralSucc, ih, Nat.cast_succ]

private theorem root_control (site : Nat) (gap : M) (args : Fin 11 → M) :
    π₁ (PA194HXFrame.frame site gap args) = (24 : M) := by
  simp only [PA194HXFrame.frame, modelPairCode, pi₁_pair, numeralCast, Nat.cast_ofNat]

private theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) :
    ConPA.Machine.step PA194HXDispatch.table y = y := by
  have eq : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h, pair_unpair, pair_unpair]
  conv_lhs => rw [eq]
  rw [PA194HXDispatch.haltFixed, ← eq]

theorem startup_root :
    ConPA.Machine.run PA194HXDispatch.table (56134 : M) =
      F PA194HXSourceRoot.sourceRootCode ![initialSource, 0, modelNumeral M 25, initialSpare] := by
  rw [PA194HXSourceRoot.sourceRootCodeCorrect _ _ _ _ ⟨25, by decide⟩ initialPC,
    seedArguments, zero_add]
  have gap : 48 - (PA194SourceProgram.path 25).length = 42 := by
    rw [PA194Path27Frame.path25]
    rfl
  rw [gap]
  exact PA194HXSeedFrame.reachesFrame

/-- The actual HX blank run agrees on halting with the shared source controller. -/
theorem endpoint (checks : PA194HXControllerAdvance.AllContracts) :
    (∃ t : M, π₁ (ConPA.Machine.run PA194HXDispatch.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n, initialSource]] = modelNumeral M 3674 := by
  refine PA194VariantController.halt_iff_controller PA194HXDispatch.table 194
    PA194HXSourceRoot.sourceRootCode initialSource (56134 : M) initialSpare 0 (modelNumeral M 25)
    ?_ startup_root ?_ halt_absorbs ?_ ?_
  · rw [initialPC]
    exact modelNumeralStrict 25 3673 (by decide)
  · intro s gap count bound
    obtain ⟨site, pc_eq⟩ := modelBelowNumeral 3673 (F pc ![s]) bound
    rw [PA194HXSourceRoot.sourceRootCodeCorrect _ _ _ _ site pc_eq, root_control]
    norm_num
  · intro s gap count bound normal
    obtain ⟨nextGap, nextCount, pc_bound, duration, positive, run_eq⟩ :=
      PA194HXControllerAdvance.advance checks initialSpare s bound normal gap count
    exact ⟨duration, nextGap, nextCount, positive, pc_bound, run_eq⟩
  · intro s gap count halt_site
    obtain ⟨final, ⟨duration, _, run_eq⟩, halted⟩ :=
      PA194HXControllerHalt.site10Halts s gap count initialSpare halt_site
    exact ⟨duration, run_eq.symm ▸ halted⟩

#print axioms startup_root
#print axioms endpoint
end models
end PA194HXSourceEndpoint
