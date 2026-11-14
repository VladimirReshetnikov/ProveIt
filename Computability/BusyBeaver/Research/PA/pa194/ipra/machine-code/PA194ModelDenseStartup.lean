import PA194PackedNumeralBridge
import PA194DenseStartupComplete
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ModelDenseStartup
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHistoryPairCode
open TableDispatch PA194PackedNumeralBridge

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)

/-- The literal blank machine's 58,154-step startup reaches the exact encoded
source seed frame, in every candidate PRA model. Its time is the indicated
external standard numeral; no nonstandard-duration simulation is asserted. -/
theorem modelDenseStartup :
    F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0] =
      F pairCode ![modelNumeral M 24,
        F pairCode ![modelNumeral M 1,
          modelNumeral M (PA194Bounded.bits PA194StartupData.seedFrame.r)]] := by
  let finish : M6.Zip.Conf := ⟨24,PA194StartupData.seedFrame.l,PA194StartupData.seedFrame.r⟩
  have hs : M6.Zip.run PA194.Literal.machine 58154 PA194Bounded.blankZip = some finish := by
    exact PA194DenseStartupComplete.startup_exact
  have hh := literalBlankRun_explicitEndpoint (M := M) 58154 finish hs
  have hl : PA194StartupData.seedFrame.l = [true] := by
    rw [← PA194StartupData.last_eq]
    rfl
  change F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0] =
      F pairCode ![modelNumeral M 24,
        F pairCode ![modelNumeral M (PA194Bounded.bits PA194StartupData.seedFrame.l),
          modelNumeral M (PA194Bounded.bits PA194StartupData.seedFrame.r)]] at hh
  rw [hl] at hh
  exact hh
#print axioms modelDenseStartup
end models
end PA194ModelDenseStartup
