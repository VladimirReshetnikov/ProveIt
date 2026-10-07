import GowersSzemeredi.Proofs16Basic

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
  classical
  induction hn : Gamma.card using Nat.strong_induction_on generalizing Gamma with
  | h n ih =>
    by_cases hsmall : ((relationProjection Gamma).card : Real) < theta * (N : Real) ^ k
    · let J := Finset.univ \ relationProjection Gamma
      refine ⟨0, Fin.elim0, J, (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
      · simp
      · have hc := Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (relationProjection Gamma))
        have hsum : (J.card : Real) + (relationProjection Gamma).card = (N : Real) ^ k := by
          exact_mod_cast (by simpa [J, Point, ZMod.card] using hc)
        linarith
      · intro z hz
        have hmem := Finset.mem_filter.mp hz
        have hp : z.1 ∈ relationProjection Gamma :=
          Finset.mem_image.mpr ⟨z, hmem.1, rfl⟩
        exact ((Finset.mem_sdiff.mp hmem.2).2 hp).elim
    · obtain ⟨D, hD, hDmass, hDgood⟩ := hextract Gamma Finset.Subset.rfl (le_of_not_gt hsmall)
      have hDpos : 0 < D.card := by exact_mod_cast hmass.trans_le hDmass
      have hcard : (Gamma \ D).card < n := by
        have hc := Finset.card_sdiff_add_card_eq_card hD
        omega
      have he : ∀ Delta ⊆ Gamma \ D,
          theta * (N : Real) ^ k ≤ (relationProjection Delta).card →
          ∃ E ⊆ Delta, mass ≤ E.card ∧ Good E := by
        intro Delta hDelta hh
        exact hextract Delta (hDelta.trans Finset.sdiff_subset) hh
      obtain ⟨q, G, J, hG, hq, hJ, hcover⟩ := ih _ hcard (Gamma \ D) he rfl
      refine ⟨q + 1, Fin.cons D G, J, ?_, ?_, hJ, ?_⟩
      · intro i
        refine Fin.cases ⟨hD, hDgood⟩ (fun j => ?_) i
        exact ⟨(hG j).1.trans Finset.sdiff_subset, (hG j).2⟩
      · have hc : ((Gamma \ D).card : Real) + D.card = Gamma.card := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card hD
        rw [hn] at hc
        push_cast
        nlinarith only [hc, hq, hDmass]
      · intro z hz
        have hm := Finset.mem_filter.mp hz
        rw [section16FinsetUnion, Finset.mem_biUnion]
        by_cases hzD : z ∈ D
        · exact ⟨0, Finset.mem_univ _, hzD⟩
        · have hzRest : z ∈ restrictRelation (Gamma \ D) J :=
            Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hm.1, hzD⟩, hm.2⟩
          obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hcover hzRest)
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
