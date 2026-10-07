import GowersSzemeredi.Proofs16BalancedAlphabetExistence
import GowersSzemeredi.Definitions

/-! Uniformly balanced words on all sufficiently long proper modular
progressions, with an explicit finite union-bound budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exists_balanced_progression_word {N R : Nat} [NeZero N] (hR : 0 < R)
    (L epsilon : Real) (hL : L ≤ N) (hε : 0 ≤ epsilon)
    (hbudget : (N : Real) ^ 2 * (N + 1) * R * Real.exp (-2 * epsilon ^ 2 * L) < 1) :
    ∃ w : ZMod N → Fin R, ∀ P : ModAP N, P.IsProper → L ≤ P.length →
      ∀ c : Fin R, ((P.carrier.filter (fun x => w x = c)).card : Real) ≤
        (1 / (R : Real) + epsilon) * P.length := by
  classical
  letI : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  let J := ZMod N × ZMod N × Fin (N + 1)
  let P (j : J) : ModAP N := ⟨j.1, j.2.1, j.2.2.val⟩
  let T (j : J) : Finset (ZMod N) :=
    if (P j).IsProper ∧ L ≤ (P j).length then (P j).carrier else Finset.univ
  have hT (j : J) : L ≤ ((T j).card : Real) := by
    dsimp only [T]
    split_ifs with h
    · rw [h.1]
      exact h.2
    · simpa only [Finset.card_univ, ZMod.card] using hL
  have hb : (Fintype.card J : Real) * Fintype.card (Fin R) * Real.exp (-2 * epsilon ^ 2 * L) < 1 := by
    simpa only [J, Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_two, mul_assoc] using hbudget
  obtain ⟨w, hw⟩ := exists_balanced_alphabet_word (C := Fin R) T L epsilon hε hT hb
  refine ⟨w, ?_⟩
  intro Q hQ hQL c
  have hQN : Q.length ≤ N := by
    rw [← hQ]
    simpa only [ZMod.card] using Q.carrier.card_le_univ
  let j : J := (Q.start, Q.step, ⟨Q.length, by omega⟩)
  have hPQ : P j = Q := by cases Q; rfl
  have hTQ : T j = Q.carrier := by simp only [T, hPQ, hQ, hQL, and_self, if_true]
  have ht := hw j c
  rw [hTQ, hQ, Fintype.card_fin] at ht
  exact ht

end LeanProofs.GowersSzemeredi
