import PA194ADInitializer
import PA194ADController
import PA194VariantController
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ADControllerEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime PA194ADCompressedData PA194ADRoot PA194ADCompressedPhysical PA194ADController
open PA194SourceControllerCode PA194CompressedStartup PA194FiniteControls PA194StateOne
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
private theorem root_control (gap : M) (box : BoxSt → M) (i extra : Nat) (effect : Eff) :
    π₁ (root gap box i extra effect) = (24 : M) := by
  rw [root,encodeControl]
  change (denseControl 84 : M) = (24 : M)
  rw [rootControl]
  rfl
private theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) : ConPA.Machine.step table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [table, PA194BModelSteps.halted rows rowCount, ← he]
theorem halt_iff_controller (checks : AllContracts) (boxes : Boxes (PA194CompressedStartup.initialSpare (M := M))) :
    (∃ t : M, π₁ (ConPA.Machine.run table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,PA194CompressedStartup.initialSource]] = modelNumeral M 3674 := by
  refine PA194VariantController.halt_iff_controller table 194 sourceRootCode initialSource (58122 : M)
    initialSpare 0 (modelNumeral M 25) ?_ PA194ADInitializer.startup_root ?_ halt_absorbs ?_
    (terminal initialSpare boxes)
  · rw [initialPC]
    exact modelNumeralStrict 25 3673 (by decide)
  · intro s gap count hpc
    obtain ⟨i, hi⟩ := modelBelowNumeral 3673 (F pc ![s]) hpc
    rw [sourceRoot_eval s gap count _ i hi, root_control]
    norm_num
  · intro s gap count hs hn
    obtain ⟨nextGap, nextCount, hpc, k, hk, hrun⟩ := advance checks _ boxes s hs hn gap count
    exact ⟨k, nextGap, nextCount, hk, hpc, hrun⟩


theorem halt_iff_controller_literal (checks : AllContracts) :
    (∃ t : M, π₁ (ConPA.Machine.run table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,PA194CompressedStartup.initialSource]] = modelNumeral M 3674 :=
  halt_iff_controller checks (literalBoxes PA194CompressedStartup.initialSpare)

#print axioms halt_iff_controller_literal
#print axioms halt_iff_controller
end models
end PA194ADControllerEndpoint
