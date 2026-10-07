import OAI.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
import OAI.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

private theorem certifiedChartMatrix_budget {ι κ : Type*}
    [Fintype ι] [Fintype κ] (matrix : Matrix ι κ ℚ)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hheight : ∀ i j, rationalLogHeight (matrix i j) ≤ ((p + 2) ^ 2 + 2) ^ 63) :
    (∀ i j, |(matrix i j : ℝ)| ≤ Real.exp (((p + 2) ^ 2 + 2) ^ 63)) ∧
    0 < matrixDenominator matrix ∧
    (matrixDenominator matrix : ℝ) ≤ Real.exp ((p + 2) ^ 254) ∧
    ∀ i j, ∃ z : ℤ, (z : ℝ) = (matrixDenominator matrix : ℝ) * (matrix i j : ℝ) := by
  have hcost : ((p + 2) ^ 2 + 2) ^ 63 ≤ (p + 2) ^ 252 := by
    simpa using shifted_power_budget_le hp 2 63
  refine ⟨fun i j => (rational_abs_real_le_numerator (matrix i j)).trans
    ((rationalLogHeight_le_iff _ _).mp (hheight i j)).1,
    matrixDenominator_pos matrix, ?_, ?_⟩
  · apply matrixDenominator_le_exp_power matrix hp 252 hι hκ
    intro i j
    exact ((rationalLogHeight_le_iff _ _).mp (hheight i j)).2.trans
      (Real.exp_le_exp.mpr hcost)
  · intro i j
    obtain ⟨z, hz⟩ := matrixDenominator_mul_entry_real_integral matrix i j
    exact ⟨z, hz.symm⟩

theorem RationalTaggedConstraintCertificate.exists_certified_chart_basis_budget
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] {X : Type*}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ) (d : ℕ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      Fintype.card (Σ j, Fin (n j)) ≤ Fintype.card (Σ j, J j) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      (∀ a x, RationalHeightLE (matrix a x) ⌈Real.exp (((p + 2) ^ 2 + 2) ^ 63)⌉₊) ∧
      (∀ a x, |(b a : (Σ j, J j) → ℝ) x| ≤ Real.exp (((p + 2) ^ 2 + 2) ^ 63)) ∧
      d = matrixDenominator matrix ∧ 0 < d ∧
      (d : ℝ) ≤ Real.exp ((p + 2) ^ 254) ∧
      (∀ a x, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (b a : (Σ j, J j) → ℝ) x) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
        (∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K) →
        ∀ v : (Σ j, J j) → ℝ, (∀ j, (fun i => v ⟨j, i⟩) ∈ U j) → v ∈ Ktag := by
  classical
  have hdimTag (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ p := by
    have hcard : Fintype.card (J j) ≤ Fintype.card (Σ j, J j) :=
      Fintype.card_le_of_injective (fun i => (⟨j, i⟩ : Σ j, J j)) sigma_mk_injective
    exact (Nat.cast_le.mpr hcard).trans hdim
  obtain ⟨n, Ktag, b, matrix, hn, hentry, hofftag, hheight, hK, hret⟩ :=
    hcert.exists_bounded_chart_tag_basis hp hdimTag hblocks
  have hcard : Fintype.card (Σ j, Fin (n j)) ≤ Fintype.card (Σ j, J j) := by
    simp only [Fintype.card_sigma, Fintype.card_fin]
    exact Finset.sum_le_sum (fun j _ => hn j)
  obtain ⟨habs, hdpos, hdbound, hgrid⟩ := certifiedChartMatrix_budget matrix hp
    ((Nat.cast_le.mpr hcard).trans hdim) hdim hheight
  refine ⟨n, Ktag, b, matrix, matrixDenominator matrix, hn, hcard, hentry,
    hofftag, hheight, fun a x => rationalHeightLE_ceil_exp (hheight a x),
    ?_, rfl, hdpos, hdbound, ?_, hK, hret⟩
  · intro a x
    rw [hentry]
    exact habs a x
  · intro a x
    rw [hentry]
    exact hgrid a x

end Erdos3.VectorPolynomial

end

end OAI
