import GowersSzemeredi.Proofs16ProgressionGoodPairImages
import GowersSzemeredi.Proofs16SelectedProgressionMaps

/-! Count pairwise bridge failures directly from the original progression
quadruple exceptions. Each failed bridge determines a unique additive
quadruple, so no new exceptional mass is introduced. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Pair/bridge failure fibres inject into the additive quadruple failures. -/
theorem column_pair_image_failures_total_le {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real) (K : Nat) :
    (∑ p ∈ C ×ˢ C, (columnPairImageFailures C T L rho K p.1 p.2).card) ≤
      (progressionMapImageFailures C T L rho K).card := by
  let S := (C ×ˢ C).sigma fun p => columnPairImageFailures C T L rho K p.1 p.2
  let q : (Sigma fun _p : ZMod N × ZMod N => ZMod N) → Fin 4 → ZMod N :=
    fun p => ![p.1.1,p.1.2,p.2,p.2+(p.1.1-p.1.2)]
  have hcard : S.card ≤ (progressionMapImageFailures C T L rho K).card := by
    apply Finset.card_le_card_of_injOn q
    · intro p hp
      obtain ⟨hpC, hpF⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hpC
      obtain ⟨hpu, hbad⟩ := Finset.mem_filter.mp hpF
      obtain ⟨hu, hv⟩ := Finset.mem_filter.mp hpu
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro j
          fin_cases j
          · simpa [q] using hpa
          · simpa [q] using hpb
          · simpa [q] using hu
          · simpa [q] using hv
        · change p.1.1-p.1.2+p.2-(p.2+(p.1.1-p.1.2)) = 0
          ring
      · change ¬ColumnQuadImageRelation T L rho K p.1.1 p.1.2 (p.2+(p.1.1-p.1.2)) p.2
        exact hbad
    · intro p hp r hr he
      have h0 : p.1.1 = r.1.1 := by simpa [q] using congrFun he 0
      have h1 : p.1.2 = r.1.2 := by simpa [q] using congrFun he 1
      have h2 : p.2 = r.2 := by simpa [q] using congrFun he 2
      have hpq : p.1 = r.1 := Prod.ext h0 h1
      cases p with | mk p1 p2 =>
        cases r with | mk r1 r2 =>
          dsimp only at hpq h2
          subst r1
          exact Sigma.ext rfl (heq_of_eq h2)
  simpa only [S, Finset.card_sigma] using hcard

/-- Markov's counting bound: few failed quadruples imply few pairs with
more than `b` failed bridges. The estimate is uniform in the threshold. -/
theorem column_bad_pairs_count_le {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real) (K b : Nat) :
    (b+1)*((C ×ˢ C).filter fun p => b < (columnPairImageFailures C T L rho K p.1 p.2).card).card ≤
      (progressionMapImageFailures C T L rho K).card := by
  let B := (C ×ˢ C).filter fun p => b < (columnPairImageFailures C T L rho K p.1 p.2).card
  calc (b+1)*B.card = ∑ _p ∈ B, (b+1) := by simp [Nat.mul_comm]
    _ ≤ ∑ p ∈ B, (columnPairImageFailures C T L rho K p.1 p.2).card :=
      Finset.sum_le_sum fun p hp => Nat.succ_le_of_lt (Finset.mem_filter.mp hp).2
    _ ≤ ∑ p ∈ C ×ˢ C, (columnPairImageFailures C T L rho K p.1 p.2).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := column_pair_image_failures_total_le C T L rho K

end LeanProofs.GowersSzemeredi
