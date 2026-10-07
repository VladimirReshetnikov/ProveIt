import OAI.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {U B : Type*} [Fintype B]

theorem majorTranslationPolynomialOrbit_integerEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (x : U → ℤ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitEval
        (fun _ : U => 1) x (majorTranslationPolynomialOrbit w d hw hwd F hF A hA)) =
      algebraicMajorSymbol F (specializeMajorParameters (RingHom.id ℝ) F 0) A
        (fun i => (x i : ℝ)) := by
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd F hF A hA _

end Erdos3.PolynomialTranslationLie

end

end OAI
