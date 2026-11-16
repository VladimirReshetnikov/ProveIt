import PAVariantModelStep
import PA194ADClock
set_option autoImplicit false
namespace PAVariantADInstance
open DiophantineConsistency
open PRAFiniteFunctionCodes ConfigurationStep

theorem nextQ_eq : PAVariantModelStep.nextQ 194 194 PA194ADTable.adRows = PA194ADNext.nextQ := rfl

theorem nextL_eq : PAVariantModelStep.nextL 194 PA194ADTable.adRows = ConfigurationStep.nextL := by
  simp only [PAVariantModelStep.nextL, PAVariantModelStep.live, PAVariantModelStep.dir,
    PAVariantModelStep.leftIfRight, PAVariantModelStep.wr, ConfigurationStep.nextL,
    ConfigurationStep.live, ConfigurationStep.c194, ConfigurationStep.dir,
    ConfigurationStep.leftIfRight, ConfigurationStep.wr]
  rw [show PAVariantRowDispatch.directionCode PA194ADTable.adRows = PA194ADDispatch.directionCode from rfl,
    show PAVariantRowDispatch.writeCode PA194ADTable.adRows = PA194ADDispatch.writeCode from rfl,
    PA194ADDispatch.directionCode_eq, PA194ADDispatch.writeCode_eq]

theorem nextR_eq : PAVariantModelStep.nextR 194 PA194ADTable.adRows = ConfigurationStep.nextR := by
  simp only [PAVariantModelStep.nextR, PAVariantModelStep.live, PAVariantModelStep.dir,
    PAVariantModelStep.rightIfLeft, PAVariantModelStep.wr, ConfigurationStep.nextR,
    ConfigurationStep.live, ConfigurationStep.c194, ConfigurationStep.dir,
    ConfigurationStep.rightIfLeft, ConfigurationStep.wr]
  rw [show PAVariantRowDispatch.directionCode PA194ADTable.adRows = PA194ADDispatch.directionCode from rfl,
    show PAVariantRowDispatch.writeCode PA194ADTable.adRows = PA194ADDispatch.writeCode from rfl,
    PA194ADDispatch.directionCode_eq, PA194ADDispatch.writeCode_eq]

#print axioms nextQ_eq
#print axioms nextL_eq
#print axioms nextR_eq
end PAVariantADInstance
