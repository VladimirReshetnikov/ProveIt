import GowersSzemeredi.Proofs16LargePowerPiece
import GowersSzemeredi.Proofs16CommonBasePieceBudget
import GowersSzemeredi.Proofs16GreedyRelations

/-! Stronger extraction with the actual common-base density. The selected
pieces and their cover profiles are unchanged; only premature mass weakening
is removed from the finite greedy count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every relation with the product property and a large projection has a
uniformly large power-covered subrelation. Only preceding structural
dimensions are assumed; the all-ones lift and its mass transport are proved. -/
theorem section16_sharp_power_piece_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N), RelationProductProperty gamma Gamma →
        theta * (N : Real) ^ (k + 1) ≤ (relationProjection Gamma).card →
        ∃ E ⊆ Gamma, section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1) ≤ E.card ∧
          Section16PowerCoverProfile theta gamma k E := by
  obtain ⟨Ns, hNs⟩ := lemma_16_4_extraction k theta gamma ht ht1 hg hg1 hth
  obtain ⟨Nc, hNc⟩ := (hth k hk le_rfl).common_base_data theta gamma ht ht1 hg hg1
  refine ⟨max 3 (max Ns Nc), fun N _ _ hN Gamma hprod hlarge => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNs' : Ns ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNc' : Nc ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  rcases hNs N hNs' ho Gamma hprod with hsmall | ⟨B, phi, hgraph, hstructured⟩
  · obtain ⟨H, hH, hsupp⟩ := hsmall
    have hsub : relationProjection Gamma ⊆ H := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hsupp z hz
    have hp : ((relationProjection Gamma).card : Real) ≤ H.card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    linarith only [hlarge, hH, hp]
  · obtain ⟨D⟩ := hNc N hNc' B phi hstructured
    refine ⟨section16TranslatedGoodGraph B phi (D.H ∩ D.J) D.Y D.x0,
      section16TranslatedGoodGraph_subset Gamma B phi _ _ _ hgraph, ?_,
      (D.power_cover_profile hstructured hk ht ht1 hg hg1).translate (appendCoordinate D.x0 0)⟩
    rw [section16TranslatedGoodGraph_card]
    exact D.good_mass

/-- After discarding a small set of projected points, a product relation
is covered by a bounded number of subrelations with explicit power-cover
profiles. The only structural assumptions are in preceding dimensions. -/
theorem section16_sharp_power_decomposition_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N (k + 1) × ZMod N),
          ∃ J : Finset (Point N (k + 1)),
            (∀ i, G i ⊆ Gamma ∧ Section16PowerCoverProfile theta gamma k (G i)) ∧
            (q : Real) ≤ section16CommonBasePieceBound theta gamma k ∧
            (1 - theta) * (N : Real) ^ (k + 1) ≤ J.card ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  obtain ⟨N0, hN0⟩ := section16_sharp_power_piece_of_dimension_induction hk hth theta gamma ht ht1 hg hg1
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  have hd : 0 < section16ThetaTwo (section16ThetaOne theta gamma k) := by
    unfold section16ThetaTwo section16ThetaOne
    positivity
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let mass := section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1)
  have hmass : 0 < mass := by dsimp [mass]; positivity
  obtain ⟨q, G, J, hG, hq, hJ, hc⟩ := section16_greedy_relation_decomposition
    (Section16PowerCoverProfile theta gamma k) theta mass hmass Gamma
    (fun Delta hDelta hlarge => hN0 N hN Delta (hprod.mono hDelta) hlarge)
  refine ⟨q, G, J, hG, ?_, hJ, hc⟩
  have hbudget : (q : Real) * mass ≤
      (section16CommonBasePieceBound theta gamma k) * mass := by
    calc
      _ ≤ (Gamma.card : Real) := hq
      _ ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) := hcard
      _ = _ := by dsimp [mass, section16CommonBasePieceBound]; field_simp
  exact (mul_le_mul_iff_left₀ hmass).mp hbudget

end LeanProofs.GowersSzemeredi
