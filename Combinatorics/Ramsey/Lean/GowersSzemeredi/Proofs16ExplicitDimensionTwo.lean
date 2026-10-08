import GowersSzemeredi.Proofs16DimensionTwo
import GowersSzemeredi.Proofs16ExplicitBaseCase
import GowersSzemeredi.Proofs15ExplicitThresholds

/-! Theorem 16.2 in dimension two with an explicit modulus threshold.

This module repeats the dimension-two proof (`section16_cubic_structured_extraction`,
`section16_cubic_product_graph_piece`, `section16_cubic_relation_piece`,
`section16_budgeted_piece_two`, `theorem_16_2_of_budgeted_piece`) with
explicit thresholds. The face restrictions use the one-dimensional base
case at every modulus (`lemma_16_3_bounded`), so they cost nothing. The
selection step costs `lemma156ExplicitThreshold 1 (theta/4) gamma`, and
choosing an odd prime costs `3`. The result is
`Theorem162AtBounded 2 section16DimTwoThreshold`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16FaceThreshold_zero (d : Nat) (gamma eps : Real) :
    section16FaceThreshold d (fun _ _ _ => 0) gamma eps = 0 := by
  simp [section16FaceThreshold]

/-- The explicit modulus threshold of Theorem 16.2 in dimension two. -/
def section16DimTwoThreshold (gamma theta : Real) : Real :=
  max 3 (lemma156ExplicitThreshold 1 (theta / 4) gamma)

/-- `section16_cubic_structured_extraction` with an explicit threshold. -/
theorem section16_cubic_structured_extraction_explicit {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      lemma156ExplicitThreshold 1 (theta / 4) gamma ≤ (N : Real) → Odd N →
      ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
        theta * (N : Real)^2 ≤ B.card → HasProductProperty B phi gamma →
        ∃ C : Finset (Point N 2), C ⊆ B ∧
          Section16StructuredPair (theta / 2) gamma C phi ∧
          Section16FinalFreimanFamilies (section16BaseFamilyBound gamma (theta / 4)) C phi := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  intro N _ _ hN ho B phi hB hprod
  obtain ⟨B0, hB0, hB0mass, hfamily⟩ :=
    section16_restrict_final_freiman_families hg hg1 ht4 ht41 B phi hprod
  have hB0dense : theta / 2 * (N : Real)^2 ≤ B0.card := by
    have hv : 0 ≤ theta * (N : Real)^2 := by positivity
    nlinarith only [hB, hB0mass, hv]
  obtain ⟨B1, hB1, hB1mass, hfaces⟩ :=
    restrict_proper_faces_common_parameter_bounded 1 (fun _ _ _ => 0)
      (fun l hl hl1 => by
        have heq : l = 1 := by omega
        subst l
        exact lemma_16_3_bounded)
      gamma (theta / 2) hg hg1 ht2 ht21 N
      (by rw [section16FaceThreshold_zero]; positivity)
      B0 phi hB0dense (hprod.mono hB0)
  have hB1dense : theta / 4 * (N : Real)^2 ≤ B1.card := by
    convert hB1mass using 1
    ring
  obtain ⟨C, hC, hcount, hrespect⟩ :=
    lemma_15_6_of_density_lower_all_explicit 1 (theta / 4) gamma ht4 ht41 hg hg1 N hN
      (Fact.out : N.Prime) ho B1 phi hB1dense (hprod.mono (hB1.trans hB0))
  refine ⟨C, hC.trans (hB1.trans hB0), ⟨hfaces.mono hC, ?_, ?_⟩,
    hfamily.mono (hC.trans hB1)⟩
  · have heq : theta / 4 * gamma / 2 = theta / 2 * gamma / 4 := by ring
    simpa only [section16ThetaOne, heq] using hcount
  · simpa only [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat,
      inv_pow] using hrespect

/-- `section16_cubic_product_graph_piece` with an explicit threshold. -/
theorem section16_cubic_product_graph_piece_explicit {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      lemma156ExplicitThreshold 1 (theta / 4) gamma ≤ (N : Real) → Odd N →
      ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
        theta * (N : Real)^2 ≤ B.card → HasProductProperty B phi gamma →
        ∃ Gamma : Finset (Point N 2 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne (theta / 2) gamma 1) * (N : Real)^2 ≤ Gamma.card ∧
          MultiplyLinearWith
            (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (section16CubicTwoExponent (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            Gamma := by
  intro N _ _ hN ho B phi hB hprod
  obtain ⟨C, hCB, hC, hf⟩ :=
    section16_cubic_structured_extraction_explicit ht ht1 hg hg1 N hN ho B phi hB hprod
  obtain ⟨Gamma, hG, hmass, hML⟩ := section16_cubic_structured_piece
    (section16BaseFamilyBound_pos gamma (theta / 4)) (by positivity) (by linarith) hg hg1 hC hf
  exact ⟨Gamma, hG.trans (Finset.image_subset_image hCB), hmass, hML⟩

/-- `section16_cubic_relation_piece` with an explicit threshold. -/
theorem section16_cubic_relation_piece_explicit {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16DimTwoThreshold gamma theta ≤ (N : Real) →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        RelationProductProperty gamma Gamma →
        theta * (N : Real)^2 ≤ (relationProjection Gamma).card →
        ∃ D ⊆ Gamma, section16CubicPieceMass theta gamma * (N : Real)^2 ≤ D.card ∧
          MultiplyLinearWith
            (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (section16CubicTwoPowerExponent (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma) D := by
  intro N _ _ hN Gamma hprod hlarge
  have hNmax : max 3 (lemma156ExplicitThreshold 1 (theta / 4) gamma) ≤ (N : Real) := hN
  have hN3real : (3 : Real) ≤ N := (le_max_left _ _).trans hNmax
  have hN3 : 3 ≤ N := by exact_mod_cast hN3real
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
  obtain ⟨D, hD, hmass, hML⟩ := section16_cubic_product_graph_piece_explicit ht ht1 hg hg1 N
    ((le_max_right _ _).trans hNmax) ho (relationProjection Gamma) phi hlarge (hprod _ phi hgraph)
  refine ⟨D, ?_, hmass, hML.cubic_two_power_control
    (section16BaseFamilyBound_pos gamma (theta / 4)) (by positivity) (by linarith) hg hg1⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hD hz)
  exact hgraph x hx

/-- `Section16BudgetedPieceAt` with modulus threshold `T gamma theta`. -/
def Section16BudgetedPieceAtBounded (k : Nat) (T : Real → Real → Real) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∃ eta s : Real, 0 < eta ∧ 1 ≤ s ∧ s ≤ eta * multipleS theta gamma k ∧
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], T gamma theta ≤ (N : Real) →
        ∀ Gamma : Finset (Point N k × ZMod N),
          (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
          RelationProductProperty gamma Gamma →
          theta * (N : Real) ^ k ≤ (relationProjection Gamma).card →
          ∃ D ⊆ Gamma, eta * (N : Real) ^ k ≤ D.card ∧ MultiplyLinear gamma s D

/-- `theorem_16_2_of_budgeted_piece` with the threshold carried through. -/
theorem theorem_16_2_of_budgeted_piece_bounded {k : Nat} {T : Real → Real → Real}
    (hpiece : Section16BudgetedPieceAtBounded k T) : Theorem162AtBounded k T := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨eta, s, heta, hs, hbudget, hN0⟩ := hpiece gamma theta hg hg1 ht ht1
  intro N _ _ hN Gamma hcard hprod
  have hS := one_le_multipleS k ht ht1 hg hg1
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hr := one_le_mul_of_one_le_of_one_le hginv hS
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply section16_multiplyLinear_of_budgeted_pieces Gamma hg hg1
    (by positivity : 0 < eta * (N : Real) ^ k) hs hr
  · calc
      (Gamma.card : Real) * s ≤ (gamma ^ (-(2 : Int)) * (N : Real) ^ k) * s :=
        mul_le_mul_of_nonneg_right hcard (by linarith only [hs])
      _ ≤ (gamma ^ (-(2 : Int)) * (N : Real) ^ k) * (eta * multipleS theta gamma k) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by ring
  · intro Delta hDelta hlarge
    exact hN0 N hN Delta ((Nat.cast_le.mpr (Finset.card_le_card hDelta)).trans hcard)
      (hprod.mono hDelta) hlarge

/-- `section16_budgeted_piece_two` with an explicit threshold. -/
theorem section16_budgeted_piece_two_bounded :
    Section16BudgetedPieceAtBounded 2 section16DimTwoThreshold := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨hs, hbudget⟩ := section16_cubic_piece_parameter_budget ht ht1 hg hg1
  refine ⟨section16CubicPieceMass theta gamma, (multipleS theta gamma 1)^8,
    section16CubicPieceMass_pos ht hg, hs, hbudget, ?_⟩
  intro N _ _ hN Gamma _ hprod hlarge
  obtain ⟨D, hD, hmass, hML⟩ :=
    section16_cubic_relation_piece_explicit ht ht1 hg hg1 N hN Gamma hprod hlarge
  exact ⟨D, hD, hmass, hML.cubic_two_source_control ht ht1 hg hg1⟩

/-- **Theorem 16.2 in dimension two with an explicit modulus threshold.** -/
theorem theorem_16_2_at_two_bounded : Theorem162AtBounded 2 section16DimTwoThreshold :=
  theorem_16_2_of_budgeted_piece_bounded section16_budgeted_piece_two_bounded

end LeanProofs.GowersSzemeredi
