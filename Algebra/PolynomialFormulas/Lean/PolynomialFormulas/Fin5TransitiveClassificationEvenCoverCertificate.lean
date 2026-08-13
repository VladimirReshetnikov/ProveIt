/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationCertificateData

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def evenDoubleCosets : Finset S5 :=
  ((doubleCosetElements 0 ∪ doubleCosetElements 1) ∪
    doubleCosetElements 4) ∪ doubleCosetElements 5

set_option maxRecDepth 100000 in
theorem even_doubleCoset_cover_certificate :
    evenDoubleCosets = evenElements := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_0_card_certificate :
    (doubleCosetElements 0).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_1_card_certificate :
    (doubleCosetElements 1).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_4_card_certificate :
    (doubleCosetElements 4).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_5_card_certificate :
    (doubleCosetElements 5).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_0_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 0 → elementClass g = .cyclic := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_1_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 1 → elementClass g = .dihedral := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_4_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 4 → elementClass g = .alternating := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_5_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 5 → elementClass g = .alternating := by
  decide

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
