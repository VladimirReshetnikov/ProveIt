/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentCharacterEvent_probability_le {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (χ : AddChar (I → ℤ) ℂ) {q : ℝ}
    (hsingle : ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤ q) :
    (FiniteProbabilityWeights.pi p).eventProbability (fun x => ∀ j, χ (column j (x j)) = 1) ≤
      q ^ Fintype.card J := by
  rw [FiniteProbabilityWeights.eventProbability_pi p (fun j x => χ (column j x) = 1)]
  calc
    _ ≤ ∏ _j : J, q := Finset.prod_le_prod₀
      (fun j _ => (p j).eventProbability_nonneg _) (fun j _ => hsingle j)
    _ = _ := by simp

theorem largeOrderAnnihilator_probability_le {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (bad : (∀ j, Ω j) → Prop) (B R : ℕ) (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hbad : ∀ x, bad x → ∃ χ : AddChar (I → ℤ) ℂ,
      B < orderOf χ ∧ orderOf χ ≤ R ∧ ∀ j, χ (column j (x j)) = 1)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤ q a) :
    (FiniteProbabilityWeights.pi p).eventProbability bad ≤
      ∑ a : Fin R, if B < a.val + 1 then
        ((a.val + 1 : ℕ) : ℝ) ^ Fintype.card I * q (a.val + 1) ^ Fintype.card J else 0 := by
  classical
  let C := Σ a : Fin R, TorsionLatticeCharacter I (a.val + 1)
  let F : C → (∀ j, Ω j) → Prop := fun c x =>
    B < c.1.val + 1 ∧ orderOf c.2.val = c.1.val + 1 ∧ ∀ j, c.2.val (column j (x j)) = 1
  have hcover (x) (hx : bad x) : ∃ c, F c x := by
    obtain ⟨χ, hB, hR, hann⟩ := hbad x hx
    let a : Fin R := ⟨orderOf χ - 1, by omega⟩
    have ha : a.val + 1 = orderOf χ := by dsimp [a]; omega
    let c : TorsionLatticeCharacter I (a.val + 1) := ⟨χ, by rw [ha]; exact pow_orderOf_eq_one χ⟩
    refine ⟨⟨a, c⟩, ?_⟩
    change B < a.val + 1 ∧ orderOf χ = a.val + 1 ∧ ∀ j, χ (column j (x j)) = 1
    exact ⟨by rwa [ha], ha.symm, hann⟩
  apply ((FiniteProbabilityWeights.pi p).eventProbability_union_bound bad F hcover).trans
  change (∑ c : Σ a : Fin R, TorsionLatticeCharacter I (a.val + 1),
    (FiniteProbabilityWeights.pi p).eventProbability (F c)) ≤ _
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro a _
  have hterm (χ : TorsionLatticeCharacter I (a.val + 1)) :
      (FiniteProbabilityWeights.pi p).eventProbability (F ⟨a, χ⟩) ≤
        if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0 := by
    by_cases hB : B < a.val + 1
    · rw [ite_eq_left hB]
      by_cases ho : orderOf χ.val = a.val + 1
      · apply ((FiniteProbabilityWeights.pi p).eventProbability_mono _ _ (fun _ h => h.2.2)).trans
        exact independentCharacterEvent_probability_le p column χ.val
          (hsingle _ hB (by omega) χ.val ho)
      · rw [(FiniteProbabilityWeights.pi p).eventProbability_false _ (fun _ h => ho h.2.1)]
        exact pow_nonneg (hq _) _
    · rw [ite_eq_right hB,
        (FiniteProbabilityWeights.pi p).eventProbability_false _ (fun _ h => hB h.1)]
  calc
    _ ≤ ∑ _χ : TorsionLatticeCharacter I (a.val + 1),
        if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0 :=
      Finset.sum_le_sum (fun χ _ => hterm χ)
    _ = (Fintype.card (TorsionLatticeCharacter I (a.val + 1)) : ℝ) *
        (if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0) := by simp
    _ ≤ ((a.val + 1 : ℕ) : ℝ) ^ Fintype.card I *
        (if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast torsionLatticeCharacter_card_le I (a.val + 1)
      · split_ifs
        · exact pow_nonneg (hq _) _
        · exact le_rfl
    _ = _ := by split_ifs <;> simp

end Erdos3

end

end OAI
