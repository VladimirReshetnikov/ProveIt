import GowersSzemeredi.Proofs16SelectedDomainTransport
import GowersSzemeredi.Proofs16ContextualInduction

/-! Exact structural induction from a chosen common-base subdomain. This
isolates an existential selection problem and does not require a unit cover
for every common-base witness or for its entire original good domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An outstanding selection theorem sufficient for the source induction.
Its threshold is uniform over structured inputs; both the common base and
the further subdomain may depend on the input. This proposition is unasserted. -/
def Section16SelectedLiftAt (k : Nat) : Prop :=
  ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        HasProductProperty B phi gamma → Section16StructuredPair theta gamma B phi →
        ∃ D : Section16CommonBaseData theta gamma B phi, Section16SelectedUnitDomain D

/-- The older universal contract would imply the selection obligation once
a common-base witness is constructed. Its premise is now refuted for k>=1
in Proofs16ContextualLiftCounterexample; the converse is not asserted. -/
theorem Section16ContextualLiftAt.selected_lift {k : Nat}
    (h : Section16ContextualLiftAt k) (hth : Theorem162At k) : Section16SelectedLiftAt k := by
  intro theta gamma ht ht1 hg hg1
  obtain ⟨Nc, hNc⟩ := hth.common_base_data theta gamma ht ht1 hg hg1
  obtain ⟨Nl, hNl⟩ := h theta gamma ht ht1 hg hg1
  refine ⟨max Nc Nl, fun N _ _ hN B phi hprod hstructured => ?_⟩
  obtain ⟨D⟩ := hNc N ((le_max_left _ _).trans hN) B phi hstructured
  exact ⟨D, D.selected_unit_domain_of_full_cover ht ht1 hg hg1
    (hNl N ((le_max_right _ _).trans hN) B phi hprod hstructured D)⟩

/-- The selected lift supplies exactly the mass and unit cover consumed by
finite greedy extraction. No separate arbitrary-witness construction or
construction threshold is needed after the structured graph is selected. -/
theorem section16_large_piece_of_selected_lift {k : Nat}
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (hlift : Section16SelectedLiftAt k) : Section16LargePieceAt (k + 1) := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨Ns, hNs⟩ := lemma_16_4_extraction k theta gamma ht ht1 hg hg1 hth
  obtain ⟨Nl, hNl⟩ := hlift theta gamma ht ht1 hg hg1
  refine ⟨max 3 (max Ns Nl), fun N _ _ hN Gamma _hcard hprod hlarge => ?_⟩
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

/-- The exact next-dimensional structural conclusion from the existential
selection obligation and the preceding structural dimensions. -/
theorem theorem_16_2_step_of_selected_lift {k : Nat}
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (hlift : Section16SelectedLiftAt k) : Theorem162At (k + 1) :=
  theorem_16_2_of_large_piece (section16_large_piece_of_selected_lift hth hlift)

/-- All source structural dimensions follow if the selected lifting problem
is solved. This conditional theorem closes no catalogue companion by itself. -/
theorem theorem_16_2_of_selected_lifting
    (hlift : ∀ k : Nat, 1 ≤ k → Section16SelectedLiftAt k) : theorem_16_2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | k
    · exact theorem_16_2_zero
    · rcases k with _ | k
      · exact lemma_16_3_holds
      · apply theorem_16_2_step_of_selected_lift
        · intro l hl hlk
          exact ih l (by omega)
        · exact hlift (k + 1) (by omega)

end LeanProofs.GowersSzemeredi
