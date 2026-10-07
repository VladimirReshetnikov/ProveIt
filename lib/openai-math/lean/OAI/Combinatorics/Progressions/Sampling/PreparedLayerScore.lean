import OAI.Combinatorics.Progressions.Estimates.PreparedLayerFreezing

namespace OAI

section

namespace Erdos3.PolynomialPatch
open scoped BigOperators

theorem exists_contributing_site_of_pos_score
    {X Ω : Type*} [Fintype Ω] {s d : ℕ}
    (A : PolynomialPatch X s d) (t : Ω → X → ℝ) (score : Ω → ℝ)
    (hscore : 0 < 𝔼 u, score u * A.value (t u)) :
    ∃ u b, A.kernel.value ((A.form.slots (t u)).residual b) ≠ 0 := by
  classical
  by_contra h
  have hz (u : Ω) : A.value (t u) = 0 := by
    have hzero : ∀ b, A.kernel.value ((A.form.slots (t u)).residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨u, b, hb⟩
    simp only [value, TriangularSlots.patchValue, hzero, tsum_zero]
  simp [hz] at hscore

namespace LowestLayerModel
open VectorPolynomial MvPolynomial
open scoped TensorProduct

theorem exists_freeze_prepared_score
    {X Ω : Type} [Fintype Ω] {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}
    (F : A.LowestLayerModel m) (L : RankPreparationFamily X (Fin D) m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1)
    (center : ∀ u, (L u).Coord → ℝ) (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u)
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hσ : 0 < σ) (domain : Set (X → ℝ))
    (hinteger : ∀ x ∈ domain, ∃ z : X → ℤ, x = fun i => (z i : ℝ))
    (hsmall : ∀ x ∈ domain, ∀ u i, |VectorPolynomial.eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ domain, ∀ i, |VectorPolynomial.eval x err i| ≤ δ)
    (hbudget : (D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ)) < 1 / 12)
    (hscoreBudget : A.kernel.lip *
      ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) ≤ σ / 16)
    (t : Ω → X → ℝ) (ht : ∀ u, t u ∈ domain) (score : Ω → ℝ)
    (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : σ / 2 ≤ 𝔼 u, score u * A.value (t u)) :
    ∃ A' : PolynomialPatch X s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * σ / 16 ≤ 𝔼 u, score u * A'.value (t u) := by
  obtain ⟨u₀, bref, href⟩ := A.exists_contributing_site_of_pos_score t score
    ((half_pos hσ).trans_le hscore)
  let : Nonempty Ω := ⟨u₀⟩
  obtain ⟨A', hLip, hweight, hclose⟩ := F.exists_freeze_prepared L ip hip c err hprepare
    β hβ center ε hε hδ domain hinteger hsmall herr (t u₀) (ht u₀) bref href hbudget
  refine ⟨A', hLip, hweight, ?_⟩
  have hcompare : (𝔼 u, score u * A.value (t u)) ≤
      (𝔼 u, score u * A'.value (t u)) + σ / 16 := by
    calc
      _ ≤ 𝔼 u, (score u * A'.value (t u) + σ / 16) := by
        apply Finset.expect_le_expect
        intro u _
        exact unit_weight_score_error (hscoreBound u) ((hclose (t u) (ht u)).trans hscoreBudget)
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  linarith

end LowestLayerModel
end Erdos3.PolynomialPatch

end

end OAI
