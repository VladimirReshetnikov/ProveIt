import PolynomialFormulas.LazardInvariantModularProductBridgeRows120To123RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows124To128RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows129To130RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows131To132RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows133To134RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows135To136RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows137To138RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows139To140RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows141To142RangeCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow143DirectCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRows144To145RangeCertificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false

/-!
The coefficientwise certificates cover the formerly infeasible tail without
unfolding a quotient-backed `MvPolynomial` equality.  This dispatcher is
deliberately split into small interval goals; each branch invokes a checked
row/range certificate and performs no new finite computation.
-/
theorem degreeSevenLiteralProduct_eq_encoded_rows120To145 :
    ∀ i : Fin 159, 120 ≤ i.1 ∧ i.1 < 146 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  by_cases h124 : i.1 < 124
  · exact rows120To123_literalProduct_eq_encoded i ⟨hi.1, h124⟩
  by_cases h129 : i.1 < 129
  · exact rows124To128_literalProduct_eq_encoded i ⟨by omega, h129⟩
  by_cases h131 : i.1 < 131
  · exact rows129To130_literalProduct_eq_encoded i ⟨by omega, h131⟩
  by_cases h133 : i.1 < 133
  · exact rows131To132_literalProduct_eq_encoded i ⟨by omega, h133⟩
  by_cases h135 : i.1 < 135
  · exact rows133To134_literalProduct_eq_encoded i ⟨by omega, h135⟩
  by_cases h137 : i.1 < 137
  · exact rows135To136_literalProduct_eq_encoded i ⟨by omega, h137⟩
  by_cases h139 : i.1 < 139
  · exact rows137To138_literalProduct_eq_encoded i ⟨by omega, h139⟩
  by_cases h141 : i.1 < 141
  · exact rows139To140_literalProduct_eq_encoded i ⟨by omega, h141⟩
  by_cases h143 : i.1 < 143
  · exact rows141To142_literalProduct_eq_encoded i ⟨by omega, h143⟩
  by_cases h144 : i.1 < 144
  · have hi143 : i.1 = 143 := by omega
    have hi' : i = ⟨143, by decide⟩ := by
      apply Fin.ext
      exact hi143
    simpa [hi'] using row143_literalProduct_eq_encoded_direct
  exact rows144To145_literalProduct_eq_encoded i ⟨by omega, hi.2⟩

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
