import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts

namespace OAI

section

namespace Erdos3
open MvPolynomial

theorem scaleMvPolynomialAxes_substitution {I J : Type*}
    (T : J → ℝ) (f : I → MvPolynomial J ℝ) (p : MvPolynomial I ℝ) :
    scaleMvPolynomialAxes T (eval₂Hom C f p) =
      eval₂Hom C (fun i => scaleMvPolynomialAxes T (f i)) p := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval]
  simp only [coe_eval₂Hom, ← eval_assoc, Function.comp_def, scaleMvPolynomialAxes_eval]

theorem scaled_substitution_coeff_bound {I J : Type*}
    (T : J → ℝ) (hT : ∀ j, 0 < T j)
    (f : I → MvPolynomial J ℝ) (p : MvPolynomial I ℝ)
    {A B : ℝ} {s : ℕ} (hB : 1 ≤ B)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B)
    (hp : ∀ α, |p.coeff α| ≤ A) (hdegree : p.totalDegree ≤ s)
    (α : J →₀ ℕ) :
    |(eval₂Hom C f p).coeff α| ≤
      ((p.support.card : ℝ) * A * B ^ s) / monomialScale T α := by
  have hmass : realPolynomialMass p ≤ p.support.card * A := by
    unfold realPolynomialMass
    exact (Finset.sum_le_sum (fun β _ => hp β)).trans_eq (by simp)
  have hsub : realPolynomialMass (scaleMvPolynomialAxes T (eval₂Hom C f p)) ≤
      p.support.card * A * B ^ s := by
    rw [scaleMvPolynomialAxes_substitution]
    exact (realPolynomialMass_substitution_le p _ hB hf hdegree).trans
      (mul_le_mul_of_nonneg_right hmass (pow_nonneg (by linarith) _))
  have h := (realPolynomialMass_coeff_le
    (scaleMvPolynomialAxes T (eval₂Hom C f p)) α).trans hsub
  rw [scaleMvPolynomialAxes_coeff, abs_mul,
    abs_of_pos (monomialScale_pos T hT α)] at h
  exact (le_div_iff₀ (monomialScale_pos T hT α)).mpr h

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module

variable {σ τ ι V : Type*}

theorem coordinate_realChartSubstitute
    [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (l : V →ₗ[ℝ] ℝ) (f : σ → MvPolynomial τ ℝ) (P : VectorPolynomial σ ℚ V) :
    coordinate l.toAddMonoidHom (Erdos3.VectorPolynomial.realChartSubstitute f P) =
      MvPolynomial.eval₂Hom MvPolynomial.C f (coordinate l.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro x
  rw [← coordinate_eval₂ l x, eval₂_realChartSubstitute, coordinate_eval₂]
  simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval_assoc, Function.comp_def]

theorem CoefficientBound.realChartSubstitute [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T : τ → ℝ) (hT : ∀ i, 0 < T i)
    (f : σ → MvPolynomial τ ℝ) {A B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B) :
    CoefficientBound b T
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * B ^ s)
      (Erdos3.VectorPolynomial.realChartSubstitute f P) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s := (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff (β) : |Q.coeff β| ≤ A := by
    change |b.repr (coefficients P β) i| ≤ A
    simpa [monomialScale] using hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le Q hQdeg
  have hbound := scaled_substitution_coeff_bound T hT f Q hB hf hQcoeff hQdeg α
  have heq := congrArg (fun q : MvPolynomial τ ℝ => q.coeff α)
    (coordinate_realChartSubstitute (b.coord i) f P)
  rw [coeff_coordinate] at heq
  change (b.coord i) (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α) = _ at heq
  change |(b.coord i) (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

end OAI
