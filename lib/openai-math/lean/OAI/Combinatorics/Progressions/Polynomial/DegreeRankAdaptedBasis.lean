import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis ι ℚ L)

theorem exists_bounded_rank_adapted_basis
    {η : Fin (s + 1) → Fin (s + 1) → Type*}
    (v : ∀ i j, η i j → F.layer i.val j.val)
    (hspan : ∀ i j, Submodule.span ℚ (Set.range (v i j)) = ⊤) {H : ℕ}
    (hv : ∀ i j a k, RationalHeightLE (e.repr (v i j a : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧ (∀ a k, RationalHeightLE (e.repr (b a) k) H) ∧
      ∀ i j, ∃ c ≤ finrank ℚ L, F.layer i j = basisTail b c := by
  let := e.finiteDimensional_of_finite
  let N := (s + 1) * (s + 1)
  let S : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let P : Fin (N + 1) → Submodule ℚ L := fun n => F.rankFlag n.val
  have hP : Antitone P := fun _ _ h => F.rankFlag_antitone h
  have hSP (n : Fin (N + 1)) : Submodule.span ℚ (S ∩ (P n : Set L)) = P n := by
    by_cases hn : n.val < (s + 1) * (s + 1)
    · obtain ⟨hi, hj⟩ := rankFlag_decode_lt hn
      let i : Fin (s + 1) := ⟨n.val / (s + 1), Nat.lt_succ_of_le hi⟩
      let j : Fin (s + 1) := ⟨n.val % (s + 1), Nat.lt_succ_of_le hj⟩
      exact span_inter_eq_of_spanning_family _ (v i j) (hspan i j) S (hv i j)
    · have heq : n.val = (s + 1) * (s + 1) := by dsimp only [N] at n; omega
      change Submodule.span ℚ (S ∩ (F.rankFlag n.val : Set L)) = F.rankFlag n.val
      rw [heq, F.rankFlag_terminal]
      exact le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) bot_le
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := F.rankFlag_zero.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hSP 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, _, hb, hflag⟩ := exists_sorted_flag_basis_from_spanning_set P hP S hS hSP
  refine ⟨b, centralLieBasis_of_finite_flag F.rankFlag b w F.rankFlag_zero F.rankFlag_terminal
    (fun _ {_ _} hy => F.rankFlag_lie_mem hy) hw hflag, hb, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := F.layer_eq_rankFlag i j
  exact ⟨weightCut w k.val, weightCut_le w k.val,
    hk.trans ((hflag k).trans (span_weight_gt_eq_basisTail b w hw k.val))⟩

theorem exists_rank_adapted_basis_logHeight
    {η : Fin (s + 1) → Fin (s + 1) → Type*}
    (v : ∀ i j, η i j → F.layer i.val j.val)
    (hspan : ∀ i j, Submodule.span ℚ (Set.range (v i j)) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hv : ∀ i j a k, rationalLogHeight (e.repr (v i j a : L) k) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧
      (∀ i j, ∃ c ≤ finrank ℚ L, F.layer i j = basisTail b c) ∧
      (∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (e i) j) ≤ (p + 3) ^ 5) ∧
      ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := hp.trans (le_add_of_nonneg_right zero_le_one)
  have hd1 : (Fintype.card ι : ℝ) ≤ p + 1 := hd.trans (le_add_of_nonneg_right zero_le_one)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd1
  obtain ⟨b, hcentral, hb, hlayer⟩ := F.exists_bounded_rank_adapted_basis e v hspan
    (fun i j a k => rationalHeightLE_ceil_exp (hv i j a k))
  have hinverse := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  refine ⟨b, hcentral, hlayer, fun j i => rationalLogHeight_le_of_height (hb j i) hHp, ?_, ?_⟩
  · intro i j
    apply rationalLogHeight_le_of_height (hinverse i j)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H hp1 hr hHp
  · intro i j k
    apply rationalLogHeight_le_of_height (hstructure i j k)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card ι)
        (Fintype.card (Fin (finrank ℚ L))) H hp1 hd1 hr hHp

end Erdos3.DegreeRankLieFiltration

end

end OAI
