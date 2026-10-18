import GowersSzemeredi.Section16

/-! The finite extraction argument at the end of Theorem 16.2.
The large-piece premise is explicit; no lifting or quantitative absorption
is assumed by this purely finite argument. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Iteratively remove large good subrelations until the remaining projection
is small. The number of removed pieces uses their actual mass and the
original relation cardinality. -/
theorem section16_greedy_relation_decomposition {N k : Nat} [NeZero N]
    (Good : Finset (Point N k × ZMod N) → Prop) (theta mass : Real) (hmass : 0 < mass)
    (Gamma : Finset (Point N k × ZMod N))
    (hextract : ∀ Delta ⊆ Gamma,
      theta * (N : Real) ^ k ≤ (relationProjection Delta).card →
      ∃ D ⊆ Delta, mass ≤ D.card ∧ Good D) :
    ∃ q : Nat, ∃ G : Fin q → Finset (Point N k × ZMod N),
      ∃ J : Finset (Point N k),
        (∀ i, G i ⊆ Gamma ∧ Good (G i)) ∧
        (q : Real) * mass ≤ Gamma.card ∧
        (1 - theta) * (N : Real) ^ k ≤ J.card ∧
        restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  induction hn : Gamma.card using Nat.strong_induction_on generalizing Gamma with
  | h n ih =>
    by_cases hsmall : ((relationProjection Gamma).card : Real) < theta * (N : Real) ^ k
    · let J := Finset.univ \ relationProjection Gamma
      refine ⟨0, Fin.elim0, J, (fun i => Fin.elim0 i), by simp, ?_, fun z hz => ?_⟩
      · have hc := Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (relationProjection Gamma))
        have hsum : (J.card : Real) + (relationProjection Gamma).card = (N : Real) ^ k := by
          exact_mod_cast (by simpa [J, Point, ZMod.card] using hc)
        linarith
      · have hmem := Finset.mem_filter.mp hz
        exact ((Finset.mem_sdiff.mp hmem.2).2 (Finset.mem_image.mpr ⟨z, hmem.1, rfl⟩)).elim
    · obtain ⟨D, hD, hDmass, hDgood⟩ := hextract Gamma Finset.Subset.rfl (le_of_not_gt hsmall)
      have hDpos : 0 < D.card := by exact_mod_cast hmass.trans_le hDmass
      have hc := Finset.card_sdiff_add_card_eq_card hD
      obtain ⟨q, G, J, hG, hq, hJ, hcover⟩ := ih _ (by omega) (Gamma \ D)
        (fun Delta hDelta => hextract Delta (hDelta.trans Finset.sdiff_subset)) rfl
      refine ⟨q + 1, Fin.cons D G, J, fun i => Fin.cases ⟨hD, hDgood⟩
        (fun j => ⟨(hG j).1.trans Finset.sdiff_subset, (hG j).2⟩) i, ?_, hJ, fun z hz => ?_⟩
      · have hc' : ((Gamma \ D).card : Real) + D.card = n := by exact_mod_cast hc.trans hn
        push_cast
        linarith
      · rw [section16FinsetUnion, Finset.mem_biUnion]
        by_cases hzD : z ∈ D
        · exact ⟨0, Finset.mem_univ _, hzD⟩
        have hm := Finset.mem_filter.mp hz
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp
          (hcover (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hm.1, hzD⟩, hm.2⟩))
        exact ⟨i.succ, Finset.mem_univ _, hi⟩

/-- The relational product property passes to every remaining relation in
the extraction process. -/
theorem RelationProductProperty.mono {N k : Nat} [NeZero N]
    {gamma : Real} {Gamma Delta : Finset (Point N k × ZMod N)}
    (h : RelationProductProperty gamma Gamma) (hsub : Delta ⊆ Gamma) :
    RelationProductProperty gamma Delta := by
  intro B phi hg
  exact h B phi (fun x hx => hsub (hg x hx))

end LeanProofs.GowersSzemeredi
