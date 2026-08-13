/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationEvenCoverCertificate
import PolynomialFormulas.Fin5TransitiveClassificationOddCoverCertificate
import Mathlib.Tactic

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def allDoubleCosets : Finset S5 := evenDoubleCosets ∪ oddDoubleCosets

theorem all_doubleCoset_cover : allDoubleCosets = Finset.univ := by
  unfold allDoubleCosets
  rw [even_doubleCoset_cover_certificate, odd_doubleCoset_cover_certificate]
  ext g
  by_cases hsign : Equiv.Perm.sign g = 1 <;>
    simp [evenElements, oddElements, hsign]

theorem exists_doubleCoset_rep (g : S5) :
    ∃ i : Fin 8, g ∈ doubleCosetElements i := by
  have hg : g ∈ allDoubleCosets := by
    rw [all_doubleCoset_cover]
    simp
  simp only [allDoubleCosets, evenDoubleCosets, oddDoubleCosets,
    Finset.mem_union] at hg
  rcases hg with heven | hodd
  · rcases heven with ((h0 | h1) | h4) | h5
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
  · rcases hodd with ((h2 | h3) | h6) | h7
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨6, h6⟩
    · exact ⟨7, h7⟩

theorem doubleCoset_class (i : Fin 8) (g : S5)
    (hg : g ∈ doubleCosetElements i) :
    elementClass g = representativeClass i := by
  fin_cases i
  · exact doubleCoset_0_class_certificate g hg
  · exact doubleCoset_1_class_certificate g hg
  · exact doubleCoset_2_class_certificate g hg
  · exact doubleCoset_3_class_certificate g hg
  · exact doubleCoset_4_class_certificate g hg
  · exact doubleCoset_5_class_certificate g hg
  · exact doubleCoset_6_class_certificate g hg
  · exact doubleCoset_7_class_certificate g hg

theorem doubleCoset_card (i : Fin 8) :
    (doubleCosetElements i).card = representativeDoubleCosetCard i := by
  fin_cases i
  · exact doubleCoset_0_card_certificate
  · exact doubleCoset_1_card_certificate
  · exact doubleCoset_2_card_certificate
  · exact doubleCoset_3_card_certificate
  · exact doubleCoset_4_card_certificate
  · exact doubleCoset_5_card_certificate
  · exact doubleCoset_6_card_certificate
  · exact doubleCoset_7_card_certificate

/-- Every permutation is a left and right `C5` translate of one table row. -/
theorem exists_rotation_decomposition (g : S5) :
    ∃ i : Fin 8, ∃ a b : Fin 5,
      g = fiveCycle ^ (a : ℕ) * representative i * fiveCycle ^ (b : ℕ) ∧
      elementClass g = representativeClass i := by
  obtain ⟨i, hi⟩ := exists_doubleCoset_rep g
  have hclass := doubleCoset_class i g hi
  rw [doubleCosetElements] at hi
  obtain ⟨ab, _, hab⟩ := Finset.mem_image.mp hi
  exact ⟨i, ab.1, ab.2, hab.symm, hclass⟩

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
