import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistUniformAmbientHaar

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def normalizedTwistAmbientRankInput {R : Type*} [Semiring R] (z : R) : R :=
  let Q := 2 * z + 4
  2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16

theorem normalizedTwistAmbient_error_budget {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {L : ℝ≥0} (hL : (L : ℝ) ≤ Real.exp P) :
    let Q := 2 * max P E + 4
    let p := normalizedTwistAmbientRankInput (max P E)
    2 * Real.exp (-Q) + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
      (L : ℝ) * Real.exp (-2 * Q) / 2 ≤ Real.exp (-E) := by
  dsimp only
  let Q := 2 * max P E + 4
  let p := normalizedTwistAmbientRankInput (max P E)
  have hz : 0 ≤ max P E := hP.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by dsimp [Q]; linarith [le_max_left P E]
  have hEQ : E + 4 ≤ Q := by dsimp [Q]; linarith only [le_max_right P E, hE]
  have hp : 2 * Q * (2 * Q + 2) ^ 4 + Q ≤ p := by
    dsimp [p, normalizedTwistAmbientRankInput, Q]
    nlinarith [pow_nonneg (show 0 ≤ 2 * (2 * max P E + 4) + 2 by positivity) 4]
  have ht : Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) ≤ Real.exp (-Q) :=
    Real.exp_le_exp.mpr (by linarith)
  have hl : (L : ℝ) * Real.exp (-2 * Q) ≤ Real.exp (-Q) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-2 * Q) :=
        mul_le_mul_of_nonneg_right (hL.trans (Real.exp_le_exp.mpr hPQ)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : 4 * Real.exp (-Q) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 4 * Real.exp (-Q) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (4 - Q) := by rw [← Real.exp_add]; rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  change 2 * Real.exp (-Q) + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
    (L : ℝ) * Real.exp (-2 * Q) / 2 ≤ _
  linarith [Real.exp_pos (-Q)]

theorem exists_normalizedTwist_uniform_ambient_haar_budget (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {P E Rrank : ℝ}, 0 ≤ P → 0 ≤ E →
      (Fintype.card X : ℝ) ≤ P → (Fintype.card (Σ j, J j) : ℝ) ≤ P →
      (L : ℝ) ≤ Real.exp P → (W.cover : ℝ) ≤ Real.exp P → (W.modulus : ℝ) ≤ Real.exp P →
      ∀ (N : X → ℕ),
      (∀ i, Real.exp ((max P E + A) ^ A) ≤ (N i : ℝ)) →
      Real.exp ((max P E + A) ^ A) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x) -
        (𝔼 x ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
          (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i))‖ ≤
        Real.exp (-E) := by
  obtain ⟨C, hC, hcomp⟩ := exists_normalizedTwist_uniform_ambient_haar_comparison m
  let B : Polynomial ℕ := (normalizedTwistAmbientRankInput Polynomial.X + Polynomial.C C) ^ C +
    3 * (2 * Polynomial.X + 4) + 16
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W P E Rrank
    hP hE hX hdim hL hcover hmod N hlarge hRrank hrank
  let z := max P E
  let Q := 2 * z + 4
  let p := normalizedTwistAmbientRankInput z
  have hz : 0 ≤ z := hP.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by dsimp [Q, z]; linarith [le_max_left P E]
  have hpQ : 3 * Q + 16 ≤ p := by
    change 3 * Q + 16 ≤ 2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16
    have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
    linarith [pow_nonneg (show 0 ≤ 2 * Q + 2 by positivity) 4]
  have hpFreq : (2 * Q + 2) ^ 4 ≤ p := by
    change (2 * Q + 2) ^ 4 ≤ 2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16
    have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
    linarith
  have hPp : P ≤ p := hPQ.trans (by linarith)
  have hb : (p + C) ^ C + 3 * Q + 16 ≤ (z + A) ^ A := by
    simpa [B, p, Q, normalizedTwistAmbientRankInput, Polynomial.eval₂_pow] using hbudget z hz
  have hpNonneg : 0 ≤ p := by linarith
  have hb' : (p + C) ^ C ≤ (z + A) ^ A := by linarith
  have h := hcomp U ν poly hp hm W (Real.exp_pos (-Q)) hQ (hdim.trans hPQ)
    (hL.trans (Real.exp_le_exp.mpr hPQ)) (by rw [Real.exp_neg, inv_inv]) hpQ hpFreq
    (hcover.trans (Real.exp_le_exp.mpr hPp)) (hmod.trans (Real.exp_le_exp.mpr hPQ)) N
    (hX.trans hPp) (fun i => (Real.exp_le_exp.mpr hb).trans (hlarge i))
    ((Real.exp_le_exp.mpr hb').trans hRrank) hrank
  exact h.trans (normalizedTwistAmbient_error_budget hP hE hL)

end Erdos3.VectorPolynomial

end

end OAI
