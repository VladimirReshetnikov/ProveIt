import OAI.Combinatorics.Progressions.Geometry.PhysicalSpatialAnalyticFactor

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped Classical NNReal

theorem exists_allocatedSlicedFactor_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G X K Y : Type*} [Fintype G] [Fintype X] [Fintype K]
      [PseudoMetricSpace Y] (selection : Fin dim ↪ G)
      {M modulus : ℕ} {p E analytic : ℝ},
      0 ≤ p → 0 ≤ E → 0 ≤ analytic →
      (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p → ((dim + 1 : ℕ) : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      ∀ (r : ℝ≥0), (r : ℝ) = allocatedEarlyRecenteredMesh X selection M modulus p E →
      ∀ (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
        (residue : Option K × X → ℤ) (stride N : X → ℕ) {τ : ℝ},
      (∀ i, 0 < N i) → (∀ i, 0 < stride i) → 0 < τ → 1 / τ ≤ Real.exp p →
      ∀ (t : X → SpatialSiteLabel (Fin dim) modulus 4 r) (site : Finset (Fin dim))
        (F : Y → ℂ) {L : ℝ≥0}, LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) → (L : ℝ) ≤ Real.exp analytic →
      (∀ v, ‖physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N r t site F v‖ ≤ 1) ∧
      LipschitzWith ⟨Real.exp ((p + E + analytic + A) ^ A), Real.exp_nonneg _⟩
        (physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N r t site F) := by
  obtain ⟨a, ha, hmeshBudget⟩ := exists_allocatedEarlyRecenteredMesh_budget m dim
  let poly : Polynomial ℕ := 4 * Polynomial.X + 3 * (Polynomial.X + Polynomial.C a) ^ a + 27
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro G X K Y _ _ _ _ selection M modulus p E analytic hp hE hanalytic hG hX hdim hM hMP hmod
    r hrEq root D base residue stride N τ hN hstride hτ hτexp t site F L hF hFb hL
  obtain ⟨hr, _, hri, _⟩ := hmeshBudget X selection hp hE hG hX hM hMP hmod
  rw [← hrEq] at hr hri
  let P := (p + E + a) ^ a + 4
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hfourP : (4 : ℝ) ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_left (pow_nonneg (by positivity) _)
  have hbox : (4 : ℝ) ≤ Real.exp P := (by linarith [Real.add_one_le_exp (4 : ℝ)] : (4 : ℝ) ≤ Real.exp 4).trans
    (Real.exp_le_exp.mpr hfourP)
  have hinv : 1 / (r : ℝ) ≤ Real.exp P := by
    rw [one_div]
    exact hri.trans (Real.exp_le_exp.mpr (by dsimp only [P]; linarith))
  have hpExp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hframe : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.add_comm] using hdim.trans hpExp
  have hnorm := physicalSpatialAnalyticContinuous_bounds root D base residue stride N r t site F
    hN hstride hτ hr hF hFb hP hbox hinv (hX.trans hpExp) hframe hτexp
  refine ⟨hnorm.1, hnorm.2.weaken ?_⟩
  apply NNReal.coe_le_coe.mp
  change Real.exp (p + p + (3 * P + 6) + (p + 8)) + (L : ℝ) ≤ _
  let B := p + p + (3 * P + 6) + (p + 8)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : Real.exp B + (L : ℝ) ≤ Real.exp (B + analytic + 1) := by
    have h1 : Real.exp B ≤ Real.exp (B + analytic) := Real.exp_le_exp.mpr (by linarith only [hanalytic])
    have h2 : (L : ℝ) ≤ Real.exp (B + analytic) := hL.trans
      (Real.exp_le_exp.mpr (by linarith only [hB]))
    calc
      _ ≤ 2 * Real.exp (B + analytic) := by linarith only [h1, h2]
      _ ≤ Real.exp 1 * Real.exp (B + analytic) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply hsum.trans (Real.exp_le_exp.mpr ?_)
  let R := p + E + analytic
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpow : (p + E + a) ^ a ≤ (R + a) ^ a :=
    pow_le_pow_left₀ (by positivity) (by dsimp only [R]; linarith only [hanalytic]) _
  have hb : B + analytic + 1 ≤ poly.eval₂ (Nat.castRingHom ℝ) R := by
    simp [poly, Polynomial.eval₂_pow]
    change B + analytic + 1 ≤ 4 * R + 3 * (R + (a : ℝ)) ^ a + 27
    dsimp only [B, P, R] at *
    linarith only [hpow, hp, hE, hanalytic]
  exact hb.trans (hpoly R hR)

end Erdos3.VectorPolynomial

end

end OAI
