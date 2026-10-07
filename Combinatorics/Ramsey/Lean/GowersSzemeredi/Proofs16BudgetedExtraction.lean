import GowersSzemeredi.Proofs16InductionAssembly

/-! Exact structural assembly with nonunit piece parameters. A piece's
cover parameter is paid for by its mass, rather than requiring every
piece to have parameter one. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Greedy extraction and the finite-union theorem consume total parameter
q*s. The mass budget therefore allows nonunit covers for individual pieces. -/
theorem section16_multiplyLinear_of_budgeted_pieces {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) {gamma theta mass s r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hmass : 0 < mass)
    (hs : 1 ≤ s) (hr : 1 ≤ r)
    (hcard : (Gamma.card : Real) * s ≤ r * mass)
    (hextract : ∀ Delta ⊆ Gamma,
      theta * (N : Real) ^ k ≤ (relationProjection Delta).card →
      ∃ D ⊆ Delta, mass ≤ D.card ∧ MultiplyLinear gamma s D) :
    ∃ J : Finset (Point N k), (1 - theta) * (N : Real) ^ k ≤ J.card ∧
      MultiplyLinear gamma r (restrictRelation Gamma J) := by
  classical
  obtain ⟨q, G, J, hG, hq, hJ, hcover⟩ :=
    section16_greedy_relation_decomposition (MultiplyLinear gamma s) theta mass hmass Gamma hextract
  refine ⟨J, hJ, ?_⟩
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hqs : (q : Real) * s ≤ r := by
    apply (mul_le_mul_iff_left₀ hmass).mp
    calc
      _ = ((q : Real) * mass) * s := by ring
      _ ≤ (Gamma.card : Real) * s := mul_le_mul_of_nonneg_right hq hs0
      _ ≤ _ := hcard
  by_cases hq0 : q = 0
  · subst q
    have hempty : section16FinsetUnion G = ∅ := by simp [section16FinsetUnion]
    rw [hempty] at hcover
    exact multiplyLinear_downward_closed_holds N k gamma r _ _ hcover
      (multiplyLinear_empty hg hg1 hr)
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hqone : (1 : Real) ≤ q := by exact_mod_cast hqpos
    have hu := BaseCase.properMultiplyLinear_finsetUnion gamma s hs G hqpos (fun i => (hG i).2)
    exact multiplyLinear_downward_closed_holds N k gamma r _ _ hcover
      (hu.mono_parameter hg hg1 (one_le_mul_of_one_le_of_one_le hqone hs) hqs)

/-- A uniform mass/parameter tradeoff sufficient for the exact source
structural theorem. This is an unasserted obligation, not a new companion. -/
def Section16BudgetedPieceAt (k : Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∃ eta s : Real, 0 < eta ∧ 1 ≤ s ∧ s ≤ eta * multipleS theta gamma k ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ Gamma : Finset (Point N k × ZMod N),
          (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
          RelationProductProperty gamma Gamma →
          theta * (N : Real) ^ k ≤ (relationProjection Gamma).card →
          ∃ D ⊆ Gamma, eta * (N : Real) ^ k ≤ D.card ∧ MultiplyLinear gamma s D

/-- The source parameter gamma^-2*S absorbs all extracted nonunit pieces
when s <= eta*S. The conclusion is precisely Theorem162At. -/
theorem theorem_16_2_of_budgeted_piece {k : Nat} (hpiece : Section16BudgetedPieceAt k) :
    Theorem162At k := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨eta, s, heta, hs, hbudget, N0, hN0⟩ := hpiece gamma theta hg hg1 ht ht1
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
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

end LeanProofs.GowersSzemeredi
