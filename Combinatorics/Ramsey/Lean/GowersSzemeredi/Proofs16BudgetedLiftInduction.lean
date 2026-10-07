import GowersSzemeredi.Proofs16BudgetedExtraction
import GowersSzemeredi.Proofs16SelectedLiftInduction
import GowersSzemeredi.Proofs16SelectionReserve
import GowersSzemeredi.Proofs16GlobalFiniteCover

/-! The exact structural induction needs a mass/parameter budget, not a
unit cover for every selected piece. The former unit-selection obligation
implies this more flexible obligation; neither is assumed to be proved. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A selected part of the actual common-base domain with prescribed
relative mass eta and cover parameter s. The payment condition on eta and
s is kept in the uniform lifting obligation below. -/
def Section16BudgetedDomain {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi) (eta s : Real) : Prop :=
  ∃ C : Finset (Point N (k + 1)), C ⊆ section16GoodDomain B (D.H ∩ D.J) D.Y D.x0 ∧
    eta * (N : Real) ^ (k + 1) ≤ C.card ∧
    MultiplyLinearFunction gamma s C (section16PhiOne phi D.x0)

/-- Keeping the full common-base mass allows the entire selection reserve
as the cover parameter, rather than demanding a unit cover. -/
theorem Section16CommonBaseData.budgeted_domain_of_full_reserve_cover
    {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (hML : MultiplyLinearFunction gamma (section16UnitSelectionReserve theta gamma k)
      (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0)) :
    Section16BudgetedDomain D (section16ThetaTwo (section16ThetaOne theta gamma k))
      (section16UnitSelectionReserve theta gamma k) := by
  refine ⟨_, Finset.Subset.rfl, ?_, hML⟩
  rw [section16GoodDomain_card]
  exact D.good_mass

/-- A small original value set supplies a cover of the entire good domain
at the affordable nonunit parameter, preserving all common-base mass. -/
theorem Section16CommonBaseData.budgeted_domain_of_value_budget
    {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hvalues : ((B.image phi).card : Real) ≤ theta⁻¹) :
    Section16BudgetedDomain D (section16ThetaTwo (section16ThetaOne theta gamma k))
      (section16UnitSelectionReserve theta gamma k) := by
  classical
  apply D.budgeted_domain_of_full_reserve_cover
  apply multiplyLinearFunction_of_global_values _ _ (B.image phi) ?_ hg hg1
    (section16UnitSelectionReserve_gt_one k ht ht1 hg hg1).le
    (hvalues.trans (section16UnitSelectionReserve_ge_inv_theta k ht ht1 hg hg1))
  intro x hx
  exact section16GoodDomain_value_image_subset B phi (D.H ∩ D.J) D.Y D.x0
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- The remaining uniform selection problem. A nonunit parameter is
permitted when the selected mass pays for it: s <= eta*S. The constants
eta and s must be chosen before the modulus and the structured input. -/
def Section16BudgetedLiftAt (k : Nat) : Prop :=
  ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ eta s : Real, 0 < eta ∧ 1 ≤ s ∧ s ≤ eta * multipleS theta gamma (k + 1) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
          HasProductProperty B phi gamma → Section16StructuredPair theta gamma B phi →
          ∃ D : Section16CommonBaseData theta gamma B phi, Section16BudgetedDomain D eta s

/-- The previous unit-selection obligation is a special case, with mass
fraction 1/S and parameter one. No converse is needed or asserted. -/
theorem Section16SelectedLiftAt.budgeted_lift {k : Nat}
    (h : Section16SelectedLiftAt k) : Section16BudgetedLiftAt k := by
  intro theta gamma ht ht1 hg hg1
  have hS := zero_lt_one.trans_le (one_le_multipleS (k + 1) ht ht1 hg hg1)
  obtain ⟨N0, hN0⟩ := h theta gamma ht ht1 hg hg1
  refine ⟨(multipleS theta gamma (k + 1))⁻¹, 1, inv_pos.mpr hS, le_rfl, ?_, N0, ?_⟩
  · simp only [inv_mul_cancel₀ hS.ne', le_refl]
  · intro N _ _ hN B phi hprod hstructured
    obtain ⟨D, C, hC, hm, hML⟩ := hN0 N hN B phi hprod hstructured
    refine ⟨D, C, hC, ?_, hML⟩
    simpa only [div_eq_mul_inv, mul_comm] using hm

/-- Translation of a budgeted selected domain gives a piece of the original
relation with exactly the same mass fraction and nonunit cover parameter. -/
theorem Section16BudgetedDomain.large_piece {N k : Nat} [NeZero N] [Fact N.Prime]
    {theta gamma eta s : Real} {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {D : Section16CommonBaseData theta gamma B phi}
    (h : Section16BudgetedDomain D eta s)
    (Gamma : Finset (Point N (k + 1) × ZMod N)) (hgraph : GraphContained B phi Gamma) :
    ∃ E ⊆ Gamma, eta * (N : Real) ^ (k + 1) ≤ E.card ∧ MultiplyLinear gamma s E := by
  obtain ⟨C, hC, hm, hML⟩ := h
  obtain ⟨E, hE, heq, hcover⟩ := section16_selected_domain_subrelation Gamma B phi
    (D.H ∩ D.J) D.Y D.x0 C hgraph hC hML
  exact ⟨E, hE, by simpa only [heq] using hm, hcover⟩

/-- The structured extraction preceding Lemma 16.10 is sufficient to
transport the budgeted lifting obligation to the exact closing argument. -/
theorem section16_budgeted_piece_of_budgeted_lift {k : Nat}
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (hlift : Section16BudgetedLiftAt k) : Section16BudgetedPieceAt (k + 1) := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨Ns, hNs⟩ := lemma_16_4_extraction k theta gamma ht ht1 hg hg1 hth
  obtain ⟨eta, s, heta, hs, hbudget, Nl, hNl⟩ := hlift theta gamma ht ht1 hg hg1
  refine ⟨eta, s, heta, hs, hbudget, max 3 (max Ns Nl), fun N _ _ hN Gamma _hcard hprod hlarge => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNs' : Ns ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNl' : Nl ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  rcases hNs N hNs' ho Gamma hprod with hsmall | ⟨B, phi, hgraph, hstructured⟩
  · obtain ⟨H, hH, hsupp⟩ := hsmall
    have hp : ((relationProjection Gamma).card : Real) ≤ H.card :=
      Nat.cast_le.mpr (Finset.card_le_card hsupp.projection_subset)
    linarith only [hlarge, hH, hp]
  · obtain ⟨D, hD⟩ := hNl N hNl' B phi (hprod B phi hgraph) hstructured
    exact hD.large_piece Gamma hgraph

/-- The exact next-dimensional structural theorem follows from the mass
budget even if no selected piece has the unit cover parameter. -/
theorem theorem_16_2_step_of_budgeted_lift {k : Nat}
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (hlift : Section16BudgetedLiftAt k) : Theorem162At (k + 1) :=
  theorem_16_2_of_budgeted_piece (section16_budgeted_piece_of_budgeted_lift hth hlift)

/-- Conditional exact induction from the budgeted selection problem.
This implication does not assert that its lifting hypotheses hold. -/
theorem theorem_16_2_of_budgeted_lifting
    (hlift : ∀ k : Nat, 1 ≤ k → Section16BudgetedLiftAt k) : theorem_16_2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | k
    · exact theorem_16_2_zero
    · rcases k with _ | k
      · exact lemma_16_3_holds
      · apply theorem_16_2_step_of_budgeted_lift
        · intro l hl hlk
          exact ih l (by omega)
        · exact hlift (k + 1) (by omega)

end LeanProofs.GowersSzemeredi
