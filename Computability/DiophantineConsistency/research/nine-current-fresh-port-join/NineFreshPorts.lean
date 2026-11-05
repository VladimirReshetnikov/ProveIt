import DiophantineConsistency.IPRANineFreshCurrent
import CurrentFourPortBytes

/-! The exact current equation syntax uses the four decoded symbolic byte lists. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.NineFreshPorts

theorem current_natural_from_bytes :
    ObjectCurrentEquation2011.naturalExpression =
      ObjectCurrentEquation2011.positiveShift
        (ObjectCurrentEquation2011.expressionAt CurrentFourPortBytes.decoded) := by
  rw [CurrentFourPortBytes.decoded_eq_ports]
  rfl

#print axioms current_natural_from_bytes
end DiophantineConsistency.NineFreshPorts
