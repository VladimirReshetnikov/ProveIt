import PA194ADPackedStandard
import PA194ADStartupComplete
import PA194ADSeed
import PA194PackedNumeralBridge
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ADStartupModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHistoryPairCode
open TableDispatch PA194StandardCodeBridge PA194PackedNumeralBridge PackedStandard
open List.Vector
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)

theorem modelClockNumeral (n : Nat) :
    F PA194ADClock.clock (fun _ => modelNumeral M n) =
      modelNumeral M (PackedStandard.pack (PA194ADTable.run PA194ADTable.adRows (0,0,0) n)) := by
  have h := (modelStandardCode (M := M) PA194ADClock.clock) (fun _ => n)
  change F PA194ADClock.clock (fun _ => modelNumeral M n) =
    modelNumeral M (eval PA194ADClock.clock (n ::ᵥ nil)) at h
  rw [PA194ADPackedStandard.evalClock] at h
  exact h

theorem startup :
    F PA194ADClock.clock (fun _ => modelNumeral M 58122) =
      F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,
        modelNumeral M 152919395647067130113387679226998336721518593]] := by
  rw [modelClockNumeral, PA194ADStartup.startup, modelNumeralPack]

theorem seedRight_eq : PA194Bounded.bits PA194StartupData.seedFrame.r =
    152919395647067130113387679226998336721518593 := by
  rw [←PA194StartupData.last_eq]
  decide +kernel

theorem startup_seed :
    F PA194ADClock.clock (fun _ => modelNumeral M 58122) =
      F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,
        modelNumeral M (PA194Bounded.bits PA194StartupData.seedFrame.r)]] := by
  rw [seedRight_eq]
  exact startup

#print axioms modelClockNumeral
#print axioms startup
#print axioms seedRight_eq
#print axioms startup_seed
end models
end PA194ADStartupModel
