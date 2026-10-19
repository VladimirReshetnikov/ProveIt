import BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240
import BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240

set_option autoImplicit false

/-!
Discharge the four concrete Rotation240 box-runtime obligations using the
numeric endpoint theorems. No runtime witness is assumed. The symbolic-step
module remains independent of this adapter, so there is no import cycle.
The proof applies to arbitrary IΣ1-model values, gaps and extra-spare counts.
The existing finite-fuel checker acceptance now gives arithmetic endpoints
without a box-runtime premise. Internal-variable symbolic fuel, complete
dispatch simulation and internal control iteration remain separate.
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor (first)
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticSymbolicStepRotation240 (value)
open ArithmeticSymbolicBoxesRotation240 (ValidValues)
open SymbolicRotation240 (Branch SConfig)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Each field is a proved concrete machine endpoint, with the exact states. -/
theorem boxRuntime : ArithmeticSymbolicStepRotation240.BoxRuntime (V := V) := by
  constructor
  · intro br values hv r extra left
    exact ArithmeticSymbolicBoxEndpointsRotation240.box_mark br values hv r extra left
  · intro br values hv r extra left
    exact ArithmeticSymbolicBoxEndpointsRotation240.box_increment br values hv r extra left
  · intro values r hv extra left
    exact ArithmeticSymbolicBoxEndpointsRotation240.box_zero_decrement values r hv extra left
  · intro values r hv extra left
    exact ArithmeticSymbolicBoxEndpointsRotation240.box_positive_decrement values r hv extra left

/-- Actual finite checker acceptance, with every box-runtime field discharged. -/
theorem verifies_sound (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : SymbolicRotation240.verifies fuel br s wanted = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values extra gap s) =
      value values extra gap wanted :=
  ArithmeticSymbolicExecutionRotation240.verifies_sound boxRuntime
    fuel br s wanted he values hv extra gap

/-- The actual finite halt checker produces a positive internal halt time. -/
theorem verifiesHalt_sound (fuel : Nat) (br : Branch) (s : SConfig)
    (he : SymbolicRotation240.verifiesHalt fuel br s = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values extra gap s)) = 0 :=
  ArithmeticSymbolicExecutionRotation240.verifiesHalt_sound boxRuntime
    fuel br s he values hv extra gap

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240
