/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationCertificateData

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def oddDoubleCosets : Finset S5 :=
  ((doubleCosetElements 2 ∪ doubleCosetElements 3) ∪
    doubleCosetElements 6) ∪ doubleCosetElements 7

set_option maxRecDepth 100000 in
theorem odd_doubleCoset_cover_certificate :
    oddDoubleCosets = oddElements := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_2_card_certificate :
    (doubleCosetElements 2).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_3_card_certificate :
    (doubleCosetElements 3).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_6_card_certificate :
    (doubleCosetElements 6).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_7_card_certificate :
    (doubleCosetElements 7).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_2_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 2 → elementClass g = .frobenius := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_3_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 3 → elementClass g = .frobenius := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_6_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 6 → elementClass g = .symmetric := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_7_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 7 → elementClass g = .symmetric := by
  decide

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
