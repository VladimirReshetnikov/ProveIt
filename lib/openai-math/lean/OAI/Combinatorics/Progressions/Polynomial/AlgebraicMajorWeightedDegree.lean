import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem majorShiftCoordinates_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (e : B → MvPolynomial U R)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) (j : B) :
    majorShiftCoordinates e j ∈ weightedSupportLE (Sum.elim v w) (w j) := by
  exact (weightedSupportLE _ _).add_mem
    (weightedSupportLE_X (Sum.elim v w) (Sum.inr j))
    (weightedSupportLE_rename_inl_ring v w (he j))

theorem majorShiftSubstitution_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (e : B → MvPolynomial U R)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) (i : U ⊕ B) :
    majorShiftSubstitution e i ∈ weightedSupportLE (Sum.elim v w) (Sum.elim v w i) := by
  cases i with
  | inl i => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl i)
  | inr j => exact majorShiftCoordinates_weightedSupportLE v w e he j

theorem majorSlowPolynomial_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (D0 : MvPolynomial B R) (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) {d : ℕ}
    (hD0 : D0 ∈ weightedSupportLE w d)
    (hE : E ∈ weightedSupportLE (Sum.elim v w) d)
    (hV : V ∈ weightedSupportLE w d)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) :
    majorSlowPolynomial D0 E V e ∈ weightedSupportLE (Sum.elim v w) d := by
  unfold majorSlowPolynomial
  apply (weightedSupportLE _ _).sub_mem
  · apply (weightedSupportLE _ _).add_mem (weightedSupportLE_rename_inr_ring v w hD0)
    exact weightedSupportLE_aeval (Sum.elim v w) (Sum.elim v w)
      (majorShiftSubstitution e) (majorShiftSubstitution_weightedSupportLE v w e he) hE
  · exact weightedSupportLE_aeval w (Sum.elim v w) (majorShiftCoordinates e)
      (majorShiftCoordinates_weightedSupportLE v w e he) hV

theorem majorRationalPolynomial_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (Q : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (a : B → MvPolynomial U R) {d : ℕ}
    (hQ : Q ∈ weightedSupportLE (Sum.elim v w) d)
    (hV : V ∈ weightedSupportLE w d)
    (ha : ∀ j, a j ∈ weightedSupportLE v (w j)) :
    majorRationalPolynomial Q V a ∈ weightedSupportLE (Sum.elim v w) d := by
  apply (weightedSupportLE _ _).add_mem hQ
  exact weightedSupportLE_aeval w (Sum.elim v w) (majorShiftCoordinates (-a))
    (majorShiftCoordinates_weightedSupportLE v w (-a)
      (fun j => (weightedSupportLE v (w j)).neg_mem (ha j))) hV

end Erdos3

end

end OAI
