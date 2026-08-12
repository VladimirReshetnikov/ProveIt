import PolynomialFormulas.LazardInvariantModularProductBridgeRows146To147ChunkedCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows148To149ChunkedCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows150To151ChunkedCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows152To153ChunkedCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows154To155ChunkedCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows156To157ChunkedCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows158To158ChunkedCertificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false

/-! Coefficientwise dispatch for the final thirteen modular product rows. -/
theorem degreeSevenLiteralProduct_eq_encoded_rows146To158 :
    ∀ i : Fin 159, 146 ≤ i.1 ∧ i.1 < 159 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  by_cases h148 : i.1 < 148
  · have hi146 : i.1 = 146 ∨ i.1 = 147 := by omega
    rcases hi146 with h | h
    · have hi' : i = ⟨146, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row146_literalProduct_eq_encoded_direct
    · have hi' : i = ⟨147, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row147_literalProduct_eq_encoded_direct
  by_cases h150 : i.1 < 150
  · have hi148 : i.1 = 148 ∨ i.1 = 149 := by omega
    rcases hi148 with h | h
    · have hi' : i = ⟨148, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row148_literalProduct_eq_encoded_direct
    · have hi' : i = ⟨149, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row149_literalProduct_eq_encoded_direct
  by_cases h152 : i.1 < 152
  · have hi150 : i.1 = 150 ∨ i.1 = 151 := by omega
    rcases hi150 with h | h
    · have hi' : i = ⟨150, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row150_literalProduct_eq_encoded_direct
    · have hi' : i = ⟨151, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row151_literalProduct_eq_encoded_direct
  by_cases h154 : i.1 < 154
  · have hi152 : i.1 = 152 ∨ i.1 = 153 := by omega
    rcases hi152 with h | h
    · have hi' : i = ⟨152, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row152_literalProduct_eq_encoded_direct
    · have hi' : i = ⟨153, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row153_literalProduct_eq_encoded_direct
  by_cases h156 : i.1 < 156
  · have hi154 : i.1 = 154 ∨ i.1 = 155 := by omega
    rcases hi154 with h | h
    · have hi' : i = ⟨154, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row154_literalProduct_eq_encoded_direct
    · have hi' : i = ⟨155, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row155_literalProduct_eq_encoded_direct
  by_cases h158 : i.1 < 158
  · have hi156 : i.1 = 156 ∨ i.1 = 157 := by omega
    rcases hi156 with h | h
    · have hi' : i = ⟨156, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row156_literalProduct_eq_encoded_direct
    · have hi' : i = ⟨157, by decide⟩ := by apply Fin.ext; exact h
      simpa [hi'] using row157_literalProduct_eq_encoded_direct
  have hi158 : i.1 = 158 := by omega
  have hi' : i = ⟨158, by decide⟩ := by
    apply Fin.ext
    exact hi158
  simpa [hi'] using row158_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
