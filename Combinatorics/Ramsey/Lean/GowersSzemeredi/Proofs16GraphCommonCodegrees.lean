import GowersSzemeredi.Proofs16GraphPruning

/-! A dense set whose vertex pairs have many simultaneous high-codegree partners. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- Two vertices with few marked neighbours have many jointly unmarked neighbours. -/
theorem jointly_unmarked_card {V : Type*} (S : Finset V) (B : V → V → Prop) (u v : V)
    (hu : ((S.filter (B u)).card : Real) ≤ (S.card : Real)/4)
    (hv : ((S.filter (B v)).card : Real) ≤ (S.card : Real)/4) :
    (S.card : Real)/2 ≤ ((S.filter (fun z => ¬B u z ∧ ¬B v z)).card : Real) := by
  let M := S.filter (fun z => ¬B u z ∧ ¬B v z)
  have hcover : S ⊆ M ∪ (S.filter (B u) ∪ S.filter (B v)) := by
    intro z hz
    by_cases hzu : B u z
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzu⟩))
    · by_cases hzv : B v z
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hzv⟩))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzu, hzv⟩)
  have hcard : S.card ≤ M.card + (S.filter (B u)).card + (S.filter (B v)).card := by
    have h := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have h' := Finset.card_union_le (S.filter (B u)) (S.filter (B v))
    omega
  have hR : (S.card : Real) ≤ M.card + (S.filter (B u)).card + (S.filter (B v)).card := by exact_mod_cast hcard
  dsimp only [M] at hR
  linarith

/-- Retain a positive fraction of the vertices; every pair has many
vertices with large codegree to both endpoints. -/
theorem exists_dense_common_codegree_set {V : Type*} [Fintype V] [Nonempty V]
    (G : V → V → Prop) (hG : ∀ a b, G a b → G b a) {delta : Real} (hd : 0 < delta)
    (hedges : delta * (Fintype.card V : Real)^2 ≤ ∑ x : V, ((graphNeighbours G x).card : Real)) :
    ∃ T : Finset V, 3*delta*Fintype.card V/8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T,
        delta*Fintype.card V/4 ≤ ((Finset.univ.filter (fun z =>
          delta^2*Fintype.card V/64 ≤ ((graphCommonNeighbours G u z).card : Real) ∧
          delta^2*Fintype.card V/64 ≤ ((graphCommonNeighbours G v z).card : Real))).card : Real) := by
  obtain ⟨x, hsize, hbad⟩ := exists_large_neighbourhood_few_bad_pairs G hG hd hedges
  let S := graphNeighbours G x
  let B (u v : V) := (graphCommonNeighbours G u v).card < delta^2*Fintype.card V/64
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    have hn : (0 : Real) < Fintype.card V := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
    have hpos : (0 : Real) < S.card := lt_of_lt_of_le (by positivity) hsize
    exact_mod_cast hpos
  have heq : ((S ×ˢ S).filter (fun p => B p.1 p.2)) =
      graphBadPairs G (delta^2*Fintype.card V/64) x := by
    ext p
    simp [S, B, graphNeighbours, graphBadPairs, and_assoc]
  obtain ⟨T, hTS, hT, hgood⟩ := exists_subset_few_marked_neighbours S hS B (heq.symm ▸ hbad)
  refine ⟨T, by dsimp only [S] at hT; linarith, ?_⟩
  intro u hu v hv
  have h := jointly_unmarked_card S B u v (hgood u hu) (hgood v hv)
  have hsub : (S.filter (fun z => ¬B u z ∧ ¬B v z)) ⊆ Finset.univ.filter (fun z =>
      delta^2*Fintype.card V/64 ≤ ((graphCommonNeighbours G u z).card : Real) ∧
      delta^2*Fintype.card V/64 ≤ ((graphCommonNeighbours G v z).card : Real)) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      le_of_not_gt (Finset.mem_filter.mp hz).2.1, le_of_not_gt (Finset.mem_filter.mp hz).2.2⟩
  have hc : (((S.filter (fun z => ¬B u z ∧ ¬B v z))).card : Real) ≤ _ :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  dsimp only [S] at h
  linarith

end LeanProofs.GowersSzemeredi
