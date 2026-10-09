import GowersSzemeredi.Proofs16CoherentColumnPairs

/-! Orient a dense pair family before reflecting it, so that opposite
difference fibres are never joined without a consistency argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Retain at least half the pairs, with opposite selected differences
possible only when the difference equals its own negative. -/
theorem exists_oriented_pair_subset {N : Nat} [NeZero N]
    (P : Finset (ZMod N × ZMod N)) :
    ∃ S ⊆ P, P.card ≤ 2 * S.card ∧
      ∀ p ∈ S, ∀ q ∈ S, p.1-p.2 = -(q.1-q.2) → p.1-p.2 = -(p.1-p.2) := by
  let H (p : ZMod N × ZMod N) := (p.1-p.2).val ≤ (-(p.1-p.2)).val
  let S := P.filter H
  let T := P.filter (fun p => ¬ H p)
  have hsum : S.card + T.card = P.card := Finset.card_filter_add_card_filter_not _
  by_cases hsize : T.card ≤ S.card
  · refine ⟨S, Finset.filter_subset _ _, by omega, ?_⟩
    intro p hp q hq hd
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    dsimp [H] at hp' hq'
    rw [hd, neg_neg] at hp'
    have heq : (q.1-q.2).val = (-(q.1-q.2)).val := Nat.le_antisymm hq' hp'
    have hqeq := (ZMod.val_injective N) heq
    rw [hd, neg_neg]
    exact hqeq.symm
  · refine ⟨T, Finset.filter_subset _ _, by omega, ?_⟩
    intro p hp q hq hd
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    dsimp [H] at hp' hq'
    rw [hd, neg_neg] at hp'
    omega

/-- In an odd prime target, a self-opposite difference is zero. -/
theorem prime_self_opposite_zero {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 2 < N) {a : ZMod N} (ha : a = -a) : a = 0 := by
  have htwo : (2 : ZMod N) ≠ 0 := by
    intro h
    have hd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hN) hd
  have hmul : (2 : ZMod N) * a = 0 := by linear_combination ha
  exact (mul_eq_zero.mp hmul).resolve_left htwo

end LeanProofs.GowersSzemeredi
