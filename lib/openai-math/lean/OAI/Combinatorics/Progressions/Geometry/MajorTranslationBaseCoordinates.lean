import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem bchRealTranslationHom_base_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) (i : B) :
    (bchRealTranslationHom w d hwd g).base i =
      ((weightedBasis w d hw).baseChange ℝ).repr g.coord (Sum.inl i) := by
  obtain ⟨b, P, hb, _⟩ := realShearEmbedding_shape w d g.coord
  have hact := congrArg (fun f : MvPolynomial (B ⊕ Unit) ℝ ≃ₐ[ℝ]
      MvPolynomial (B ⊕ Unit) ℝ => f (X (Sum.inl i)))
    (bchRealTranslationHom_action w d hwd g)
  change PolynomialTranslationGroupOver.actionHom (bchRealTranslationHom w d hwd g)
    (X (Sum.inl i)) = polynomialShearExp (realShearEmbedding w d g.coord)
      (X (Sum.inl i)) at hact
  rw [PolynomialTranslationGroupOver.actionHom_X_inl,
    polynomialShearExp_X_of_derivation_eq_C _ _ _ (hb i)] at hact
  have hbase : (bchRealTranslationHom w d hwd g).base i = b i := by
    simpa using congrArg (fun polynomial : MvPolynomial (B ⊕ Unit) ℝ => polynomial.coeff 0) hact
  have hcoord := realShearEmbedding_base_coeff w d hw g.coord i
  rw [hb i] at hcoord
  exact hbase.trans (by simpa using hcoord)

theorem majorTranslationPolynomialOrbit_base_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) (i : B) :
    VectorPolynomial.coordinate
      (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA).log = A i := by
  apply MvPolynomial.funext
  intro u
  rw [← VectorPolynomial.coordinate_eval₂]
  change ((weightedBasis w d hw).baseChange ℝ).repr
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)).coord
        (Sum.inl i) = eval u (A i)
  rw [← bchRealTranslationHom_base_coordinate w d hw hwd,
    majorTranslationPolynomialOrbit_realEval]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
