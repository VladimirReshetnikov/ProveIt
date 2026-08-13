/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationGenerationCore

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

set_option maxRecDepth 100000 in
theorem cyclic_generation_certificate :
    generatedStage (representative 0) (representativeDepth 0) =
      classElements (representativeClass 0) := by
  decide

set_option maxRecDepth 100000 in
theorem dihedral_generation_certificate :
    generatedStage (representative 1) (representativeDepth 1) =
      classElements (representativeClass 1) := by
  decide

set_option maxRecDepth 100000 in
theorem frobenius0_generation_certificate :
    generatedStage (representative 2) (representativeDepth 2) =
      classElements (representativeClass 2) := by
  decide

set_option maxRecDepth 100000 in
theorem frobenius1_generation_certificate :
    generatedStage (representative 3) (representativeDepth 3) =
      classElements (representativeClass 3) := by
  decide

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
