import GowersSzemeredi.Proofs16CubicGraphWidthBudget
import GowersSzemeredi.Proofs16CubicPieceParameterBudget
import GowersSzemeredi.Proofs16BudgetedExtraction

/-! The exact Section 16 structural theorem in dimension two. Actual
cubic-controlled pieces meet both source budgets at parameter U^8; their
positive mass pays for the union parameter in the greedy decomposition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearWith.cubic_two_source_control {N : Nat} [NeZero N]
    {theta gamma : Real} {Gamma : Finset (Point N 2 × ZMod N)}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (h : MultiplyLinearWith
      (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
      (section16CubicTwoPowerExponent (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma) Gamma) :
    MultiplyLinear gamma ((multipleS theta gamma 1)^8) Gamma := by
  let s := (multipleS theta gamma 1)^8
  let q := section16BaseFamilyBound gamma (theta / 4)
  have hq : 0 < q := section16BaseFamilyBound_pos gamma (theta / 4)
  have hs : 0 < s := by dsimp [s]; unfold multipleS; positivity
  have h' := h.cubic_two_algebraic_control hq (by positivity) (by linarith) hg hg1
  change MultiplyLinearWith (fun rho => (multipleQ (s⁻¹ * rho) gamma 2)^s)
    (fun rho => (multipleC (s⁻¹ * rho) gamma 2)^s) Gamma
  apply h'.weaken
  · intro rho hr hr1
    have hE := section16CubicTwoAlgebraicExponent_pos hq
      (by positivity : 0 < theta / 2) hg hr
    have hC := multipleC_pos 2 (mul_pos (inv_pos.mpr hs) hr) hg
    have hCE : 0 < (multipleC (s⁻¹ * rho) gamma 2)^s := Real.rpow_pos_of_pos hC s
    have hw := section16_cubic_source_width ht ht1 hg hg1 hr hr1
    have hb := section16_cubic_graph_width_budget hq
      (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1 hr hr1
    calc
      _ ≤ (section16CubicTwoAlgebraicExponent q (theta / 2) gamma rho)⁻¹ := by
        rw [← one_div]
        exact (le_div_iff₀ hE).mpr hb
      _ ≤ ((multipleC (s⁻¹ * rho) gamma 2)^s)⁻¹ := (inv_le_inv₀ hE hCE).mpr hw
      _ = _ := by rw [multipleQ, Real.inv_rpow hC.le]
  · intro rho hr _
    exact Real.rpow_pos_of_pos (multipleC_pos 2 (mul_pos (inv_pos.mpr hs) hr) hg) s
  · intro rho hr hr1
    exact section16_cubic_source_width ht ht1 hg hg1 hr hr1

/-- The cubic extraction satisfies the exact nonunit piece budget. -/
theorem section16_budgeted_piece_two : Section16BudgetedPieceAt 2 := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨hs, hbudget⟩ := section16_cubic_piece_parameter_budget ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := section16_cubic_relation_piece ht ht1 hg hg1
  refine ⟨section16CubicPieceMass theta gamma, (multipleS theta gamma 1)^8,
    section16CubicPieceMass_pos ht hg, hs, hbudget, N0, ?_⟩
  intro N _ _ hN Gamma _ hprod hlarge
  obtain ⟨D, hD, hmass, hML⟩ := hN0 N hN Gamma hprod hlarge
  exact ⟨D, hD, hmass, hML.cubic_two_source_control ht ht1 hg hg1⟩

/-- The manuscript's structural conclusion and quantitative parameter,
proved for arbitrary two-dimensional product relations. -/
theorem theorem_16_2_at_two : Theorem162At 2 :=
  theorem_16_2_of_budgeted_piece section16_budgeted_piece_two

end LeanProofs.GowersSzemeredi
