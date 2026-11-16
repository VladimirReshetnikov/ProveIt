import PA194RegisterControllerAdvance
import PA194CompressedStartup
import PA194VariantController

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194RegisterControllerEndpoint
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194CompressedStartup PA194Path27Header
open PA194RegisterLayout PA194RegisterRoot PA194RegisterControllerAdvance
open PA194RegisterControllerStep PA194RegisterContracts
open ConPA.Machine.Compressed

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

private theorem root_control (site : Nat) (gap packed : M) :
    π₁ (frame site gap packed) = (24 : M) := by
  simp only [frame, modelPairCode, pi₁_pair, numeralCast, Nat.cast_ofNat]

private theorem halt_absorbs (rows : List PA194BRows.Action) (length : rows.length = 388)
    (y : M) (h : π₁ y = (194 : M)) :
    ConPA.Machine.step (PA194BModelSteps.table rows) y = y := by
  have eq : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h, pair_unpair, pair_unpair]
  conv_lhs => rw [eq]
  rw [PA194BModelSteps.halted rows length, ← eq]

/-- A selector variant with the primary source addresses inherits the modeled
halting comparison from its checked startup, boxes, and source contracts. -/
theorem endpoint (A : Allocation) (rows : List PA194BRows.Action)
    (length : rows.length = 388) (machine : M6.Zip.TMN) (label : Nat → Nat)
    (rowAgreement : RowAgreement (PA194BModelSteps.table rows) machine label)
    (rootControl : label 84 = 24) (haltControl : label 254 = 194)
    (boxes : Boxes (M := M) (PA194BModelSteps.table rows) label)
    (checks : AllContracts A machine)
    (haltCheck : PA194SourceContracts.haltContract machine PA194SourceProgram.path 10 512 = true)
    (startup : M)
    (initial : ConPA.Machine.run (PA194BModelSteps.table rows) startup =
      F (sourceRootCode A) ![initialSource, 0, modelNumeral M 25, initialSpare]) :
    (∃ t : M, π₁ (ConPA.Machine.run (PA194BModelSteps.table rows) t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n, initialSource]] = modelNumeral M 3674 := by
  refine PA194VariantController.halt_iff_controller (PA194BModelSteps.table rows) 194
    (sourceRootCode A) initialSource startup initialSpare 0 (modelNumeral M 25)
    ?_ initial ?_ (halt_absorbs rows length) ?_ ?_
  · rw [initialPC]
    exact modelNumeralStrict 25 3673 (by decide)
  · intro s gap count bound
    obtain ⟨site, pc_eq⟩ := modelBelowNumeral 3673 (F pc ![s]) bound
    rw [sourceRootCodeCorrect A _ _ _ _ site pc_eq, root_control]
    norm_num
  · intro s gap count bound normal
    obtain ⟨nextGap, nextCount, pc_bound, duration, positive, run_eq⟩ :=
      advance A rowAgreement rootControl boxes checks initialSpare s bound normal gap count
    exact ⟨duration, nextGap, nextCount, positive, pc_bound, run_eq⟩
  · intro s gap count halt_site
    obtain ⟨final, ⟨duration, _, run_eq⟩, halted⟩ :=
      haltAt A rowAgreement rootControl haltControl boxes haltCheck s gap count initialSpare halt_site
    exact ⟨duration, run_eq.symm ▸ halted⟩

#print axioms endpoint
end models
end PA194RegisterControllerEndpoint
