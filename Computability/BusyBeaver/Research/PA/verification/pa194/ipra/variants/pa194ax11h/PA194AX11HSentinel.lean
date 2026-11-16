import PA194AX11HSource
import PA194SourceSentinel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HSentinel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerBinding PA194SourceSentinel
open PA194SourceInstructionModel PA194SourcePCBound PA194FiniteControls PA194StateOne

theorem site10_row : PA194AX11HSource.program[10]'(by rw [PA194AX11HSource.program_length]; decide) = some .halt := by decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem site10_step (s : M) (hs : F pc ![s] = modelNumeral M 10) :
    F PA194AX11HSource.step ![s] = pair (modelNumeral M 3674) (pi₂ s) := by
  rw [PA194AX11HSource.selected 10 (by decide) s hs,site10_row]
  rfl

theorem site10_next_halted (s : M) (hs : F pc ![s] = modelNumeral M 10) :
    F pc ![F PA194AX11HSource.step ![s]] = modelNumeral M 3674 := by
  rw [site10_step s hs,pcModel,pi₁_pair]

theorem stepHalted (s : M) (hs : F pc ![s] = modelNumeral M 3674) :
    F PA194AX11HSource.step ![s] = s := by
  have ha : ∀ k : Nat, 0 ≤ k → k < 0 + PA194AX11HSource.program.length →
      F pc ![s] ≠ modelNumeral M k := by
    intro k _ hk
    have hk' : k < 3671 := by simpa [PA194AX11HSource.program_length] using hk
    rw [hs]
    exact ne_of_gt (modelNumeralStrict k 3674 (by omega))
  rw [PA194AX11HSource.step,dispatchAvoid 0 PA194AX11HSource.program s ha,defaultHalted s hs]

#print axioms site10_row
#print axioms site10_next_halted
#print axioms stepHalted
end models
end PA194AX11HSentinel
