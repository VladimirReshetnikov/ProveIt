import DiophantineConsistency.PRAHistoryTermCoreCode
import ZFCinPA.Instances
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySetTermCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA PRAFiniteFunctionCodes PRALanguage PRATheory

theorem PRA_has_setTermCoreCode :
    ∃ c : Code 2, PRA ⊢ PRACharacteristicBit.bitSentence c ∧
      PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence c
        (PRAHistoryTermCoreCode.sigmaCore (L := ℒₛₑₜ)) ∧
      PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence c
        (PRAHistoryTermCoreCode.piCore (L := ℒₛₑₜ)) := by
  exact PRAHistoryTermCoreCode.PRA_has_termCoreCode (L := ℒₛₑₜ) rfl

theorem PRA_has_setTermSuccCode : ∃ c : Code 2,
    PRA ⊢ PRAHistoryFixpointSuccCode.graphSentence (FormalizedTerm.blueprint ℒₛₑₜ) c := by
  exact PRAHistoryTermCoreCode.PRA_has_termSuccCode (L := ℒₛₑₜ) rfl
end DiophantineConsistency.PRAHistorySetTermCode
