import DiophantineConsistency.Compact44.CompactHighPopulation
import Mathlib.Data.List.GetD
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace HighTargetDigits
open CompactHighPopulation

theorem target4393 : highDigits.getD 4393 0 = mu := by decide +kernel

theorem target5495 : highDigits.getD 5495 0 = mu := by decide +kernel
#print axioms HighTargetDigits.target4393
#print axioms HighTargetDigits.target5495
end HighTargetDigits
