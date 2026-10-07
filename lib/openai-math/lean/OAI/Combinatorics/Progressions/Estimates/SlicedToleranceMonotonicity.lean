import OAI.Combinatorics.Progressions.Polynomial.SlicedPolynomialPerturbation

namespace OAI

section

namespace Erdos3

theorem slicedPrincipalBoundaryRadius_antitone {N N' : ℕ} (hN : N ≤ N')
    {η : ℝ} (hη : 0 ≤ η) :
    slicedPrincipalBoundaryRadius N' η ≤ slicedPrincipalBoundaryRadius N η := by
  unfold slicedPrincipalBoundaryRadius
  apply min_le_min le_rfl
  apply div_le_div_of_nonneg_left hη (by positivity)
  gcongr

theorem slicedPrincipalComparisonBudget_mono {N N' m : ℕ} (hN : N ≤ N')
    {C A r r' κ κ' : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hr' : 0 < r') (hr : r' ≤ r) (hκ' : 0 < κ') (hκ : κ' ≤ κ) :
    slicedPrincipalComparisonBudget N m C A r κ ≤
      slicedPrincipalComparisonBudget N' m C A r' κ' := by
  have hri : 0 < r := hr'.trans_le hr
  have hκi : 0 < κ := hκ'.trans_le hκ
  have hi : κ⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' hκ
  unfold slicedPrincipalComparisonBudget
  gcongr

theorem polynomialPerturbationScale_antitone {K K' M Q Q' τ : ℝ} {O O' : ℕ}
    (hK : 0 ≤ K) (hKK : K ≤ K') (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hQQ : Q ≤ Q')
    (hO : O ≤ O') :
    polynomialPerturbationScale K' M Q' τ O' ≤ polynomialPerturbationScale K M Q τ O := by
  unfold polynomialPerturbationScale
  apply min_le_min le_rfl
  apply min_le_min
  · apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    gcongr

theorem slicedPrincipalC2Tolerance_antitone {N N' O O' m : ℕ} (hN : N ≤ N') (hO : O ≤ O')
    {C a δ A η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    slicedPrincipalC2Tolerance N' O' m C a δ A η ≤ slicedPrincipalC2Tolerance N O m C a δ A η := by
  let r := slicedPrincipalBoundaryRadius N η
  let r' := slicedPrincipalBoundaryRadius N' η
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hr' : 0 < r' := (slicedPrincipalBoundaryRadius_spec N' hη).1
  have hrr : r' ≤ r := slicedPrincipalBoundaryRadius_antitone hN hη.le
  let κ := a * δ * (δ * r) ^ m
  let κ' := a * δ * (δ * r') ^ m
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have hκ' : 0 < κ' := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr') _)
  have hκκ : κ' ≤ κ := by
    dsimp only [κ, κ']
    gcongr
  exact polynomialPerturbationScale_antitone (inv_nonneg.mpr hκ.le) (inv_anti₀ hκ' hκκ)
    zero_le_one (slicedPrincipalComparisonBudget_nonneg N m hC hA hr hκ)
    (slicedPrincipalComparisonBudget_mono hN hC hA hr' hrr hκ' hκκ) hO

theorem slicedPrincipalC2Tolerance_pos_le_one (N O m : ℕ)
    {C a δ A η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    0 < slicedPrincipalC2Tolerance N O m C a δ A η ∧
      slicedPrincipalC2Tolerance N O m C a δ A η ≤ 1 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hκ : 0 < a * δ * (δ * r) ^ m := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have ht := polynomialPerturbationScale_spec (inv_nonneg.mpr hκ.le) zero_le_one
    (slicedPrincipalComparisonBudget_nonneg N m hC hA hr hκ) (half_pos hη) O
  exact ⟨ht.1, ht.2.1⟩

theorem slicedEndpointUniformScale_spec (N O m : ℕ)
    {a δ A η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    let t := slicedPolynomialScale N O N m m 1 1 a δ A η
    0 < t ∧ t ≤ 1 ∧
      ∀ (N' O' : ℕ), N' ≤ N → O' ≤ O → ∀ s : ℝ, |s| ≤ t →
        |s| * polynomialMassC2Budget N' m 1 ≤ slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  let ε := slicedPrincipalC2Tolerance N O m 1 a δ A η
  have hε := slicedPrincipalC2Tolerance_pos_le_one N O m zero_le_one ha hδ hA hη
  have hM : 0 ≤ polynomialMassC2Budget N m 1 := polynomialMassC2Budget_nonneg N m zero_le_one
  have ht : 0 < ε / (1 + polynomialMassC2Budget N m 1) := div_pos hε.1 (by positivity)
  have htε : ε / (1 + polynomialMassC2Budget N m 1) ≤ ε := div_le_self hε.1.le (by linarith)
  refine ⟨ht, htε.trans hε.2, ?_⟩
  intro N' O' hN hO s hs
  have hMN : polynomialMassC2Budget N' m 1 ≤ polynomialMassC2Budget N m 1 := by
    unfold polynomialMassC2Budget
    gcongr
  have hh := (le_div_iff₀ (by positivity : 0 < 1 + polynomialMassC2Budget N m 1)).mp hs
  have hsmall : |s| * polynomialMassC2Budget N m 1 ≤ ε := by nlinarith [abs_nonneg s]
  exact ((mul_le_mul_of_nonneg_left hMN (abs_nonneg s)).trans hsmall).trans
    (slicedPrincipalC2Tolerance_antitone hN hO zero_le_one ha hδ hA hη)

end Erdos3

end

end OAI
