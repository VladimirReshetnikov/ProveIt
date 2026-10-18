import GowersSzemeredi.Proofs16CoarseFunctionCover

/-! This module keeps `section16_coarse_relation_cover`; the rest of the
development, with its description, is in `Proofs16RegimeSplittingSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-! ### Exact coarse covers of relations with bounded fibres -/

/-- A relation whose fibres have at most `M` points is covered exactly, with no
exceptional points, by `3^k * M` constant graphs on each cell of a proper
partition whose cells have width at least `min 2 width`. -/
theorem section16_coarse_relation_cover {N k : Nat} [NeZero N] (hk : 0 < k)
    (Gamma : Finset (Point N k × ZMod N)) (M : Nat)
    (hfib : ∀ x : Point N k, (Gamma.filter fun z => z.1 = x).card ≤ M)
    (P : Box N k) (hP : P.IsProper) :
    ∃ L : Nat, ∃ R : Fin L → Box N k,
      ∃ mu : Fin L → Fin (3 ^ k * M) → Point N k → ZMod N,
        IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
        (∀ j, min 2 P.width ≤ (R j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (R j).carrier → ∀ y, (x, y) ∈ Gamma → ∃ i, y = mu j i x := by
  have hcells : ∃ L : Nat, ∃ R : Fin L → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, min 2 P.width ≤ (R j).width) ∧ ∀ j, (R j).carrier.card ≤ 3 ^ k := by
    by_cases hw : 2 ≤ P.width
    · obtain ⟨L, R, hpart, hproper, haxes, _⟩ := P.bounded_partition hP hk 2 (by omega) hw
      refine ⟨L, R, hpart, fun j => (hproper j).1,
        fun j => (min_le_left _ _).trans (hproper j).2, fun j => ?_⟩
      apply (R j).card_le_pow_of_axis_card_le
      intro i
      rw [(hproper j).1 i]
      have hh := (haxes j i).2
      omega
    · obtain ⟨L, x, hpart⟩ := box_singleton_partition P
      refine ⟨L, fun j => pointSingletonBox (x j), hpart,
        fun j => pointSingletonBox_isProper _, fun j => ?_, fun j => ?_⟩
      · rw [pointSingletonBox_width hk]
        omega
      · rw [pointSingletonBox_carrier, Finset.card_singleton]
        exact Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨L, R, hpart, hproper, hwidth, hcard⟩ := hcells
  let S : Fin L → Finset (Point N k × ZMod N) := fun j =>
    Gamma.filter fun z => z.1 ∈ (R j).carrier
  have hS (j : Fin L) : (S j).card ≤ 3 ^ k * M := by
    have hsub : S j ⊆ (R j).carrier.biUnion (fun x => Gamma.filter fun z => z.1 = x) := by
      intro z hz
      obtain ⟨hzG, hzR⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_biUnion.mpr ⟨z.1, hzR, Finset.mem_filter.mpr ⟨hzG, rfl⟩⟩
    calc (S j).card
        ≤ ((R j).carrier.biUnion (fun x => Gamma.filter fun z => z.1 = x)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ (R j).carrier, (Gamma.filter fun z => z.1 = x).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ (R j).carrier, M := Finset.sum_le_sum (fun x _ => hfib x)
      _ = (R j).carrier.card * M := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 3 ^ k * M := Nat.mul_le_mul_right _ (hcard j)
  let e := fun j : Fin L => (S j).equivFin.symm
  let mu : Fin L → Fin (3 ^ k * M) → Point N k → ZMod N := fun j i _x =>
    if hi : (i : Nat) < (S j).card then ((e j) ⟨i, hi⟩).val.2 else 0
  refine ⟨L, R, mu, hpart, hproper, hwidth, fun j i => isMultilinear_constant _, ?_⟩
  intro j x hx y hxy
  have hz : (x, y) ∈ S j := Finset.mem_filter.mpr ⟨hxy, hx⟩
  let a := (e j).symm ⟨(x, y), hz⟩
  let i : Fin (3 ^ k * M) := ⟨a.val, a.isLt.trans_le (hS j)⟩
  refine ⟨i, ?_⟩
  have hi : (i : Nat) < (S j).card := a.isLt
  dsimp only [mu]
  rw [dif_pos hi]
  have ha : (⟨i.val, hi⟩ : Fin (S j).card) = a := rfl
  rw [ha]
  simp [a]

end LeanProofs.GowersSzemeredi
