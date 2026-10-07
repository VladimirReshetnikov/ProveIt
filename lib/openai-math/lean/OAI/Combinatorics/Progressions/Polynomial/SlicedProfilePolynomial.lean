import OAI.Combinatorics.Progressions.Estimates.ActiveProfileNoise

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)
variable {I : Type*}

noncomputable def slicedProfileTailPolynomial
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ξ
    (∑ e ∈ nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d),
      MvPolynomial.monomial e.val (ε * r e))

theorem slicedProfileTailPolynomial_degree
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, (ξ k).totalDegree ≤ 1) :
    (slicedProfileTailPolynomial h d ε r ξ).totalDegree ≤ h d := by
  classical
  apply (polynomial_substitution_totalDegree_le _ ξ hξ ?_).trans (Nat.mul_one _).le
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans e.property

theorem slicedProfileTailPolynomial_mass
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, realPolynomialMass (ξ k) ≤ 1) :
    realPolynomialMass (slicedProfileTailPolynomial h d ε r ξ) ≤
      (nonprincipalCoefficientSlots
        (Subtype.val : SamplerCoefficientSlot G B h d → _)
        (canonicalPrincipalExponent h d)).card * |ε| := by
  classical
  apply (realPolynomialMass_substitution_le _ ξ (M := 1) le_rfl hξ le_rfl).trans
  simp only [one_pow, mul_one]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _e ∈ nonprincipalCoefficientSlots
        (Subtype.val : SamplerCoefficientSlot G B h d → _) (canonicalPrincipalExponent h d),
        |ε| := by
      apply Finset.sum_le_sum
      intro e _
      rw [realPolynomialMass_monomial, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hr e)
    _ = _ := by simp

theorem slicedProfileTailPolynomial_unit_mass
    (r : SamplerCoefficientSlot G B h d → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, realPolynomialMass (ξ k) ≤ 1) :
    realPolynomialMass (slicedProfileTailPolynomial h d
      (unitProfileTailSize (G := G) (B := B) h d) r ξ) ≤ 1 := by
  apply (slicedProfileTailPolynomial_mass h d _ r hr ξ hξ).trans
  have he := partitionedProfileTail_unit_sum (G := G) (B := B) h (fun _ => False) ⟨d, by simp⟩
  simpa only [partitionedProfileTerms, Finset.sum_const, nsmul_eq_mul] using he

theorem slicedProfile_eval_split
    (hd : 0 < h d) (ρ γ ε t : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ) (x : I → ℝ) :
    MvPolynomial.eval (fun k => MvPolynomial.eval x (ξ k))
      (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h d =>
        coefficientProfileCenter (principalCoefficientSlots h d) γ e +
          coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
            ρ γ (t * ε) e * r e)) =
      ρ * r (constantCoefficientSlot _ _) +
        (∑ b, (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b)) *
          ∏ v, MvPolynomial.eval x (ξ (.inr ⟨d, b, v⟩))) +
        t * MvPolynomial.eval x (slicedProfileTailPolynomial h d ε r ξ) := by
  classical
  rw [boundedProfile_polynomial_split h d hd]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    simp only [canonicalPrincipalExponent, productBlockExponent_monomial,
      map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    ring
  · simp only [slicedProfileTailPolynomial, map_sum, MvPolynomial.eval₂Hom_monomial,
      map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_monomial,
      Finsupp.prod, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

end Erdos3

end

end OAI
