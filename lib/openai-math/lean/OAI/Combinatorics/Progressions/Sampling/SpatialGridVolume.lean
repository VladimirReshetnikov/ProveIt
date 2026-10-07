/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
import OAI.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spatialGrid_card_le {A I : Type*} [Fintype A] [Fintype I]
    (H : A → ℝ) (hH : ∀ a, 1 ≤ H a)
    (t : Finset (A → (Unit ⊕ I) → ℤ))
    (ht : ∀ v ∈ t, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ) / H a| ≤ 1) :
    (t.card : ℝ) ≤ 5^(Fintype.card A * Fintype.card (Unit ⊕ I)) *
      (∏ a, ∏ _i : Unit ⊕ I, H a) := by
  classical
  let box := Fintype.piFinset (fun a => centeredIntegerBox (fun _ : Unit ⊕ I => ⌈H a⌉₊))
  have hc : t.card ≤ box.card := by
    apply Finset.card_le_card_of_injOn (fun v a => spatialStar (v a))
    · intro v hv
      apply Fintype.mem_piFinset.mpr
      intro a
      apply (mem_centeredIntegerBox _ _).mpr
      intro i
      have hpos : 0 < H a := lt_of_lt_of_le zero_lt_one (hH a)
      have hx := ht v hv a i
      rw [abs_div, abs_of_pos hpos] at hx
      have hb : |((spatialStar (v a) i : ℤ) : ℝ)| ≤ H a := (div_le_one hpos).mp hx
      exact_mod_cast hb.trans (Nat.le_ceil (H a))
    · intro v _ w _ he
      funext a
      have h := congrArg spatialUnstar (congrFun he a)
      simpa only [spatialUnstar_star] using h
  have hc' : (t.card : ℝ) ≤ ∏ a, ∏ _i : Unit ⊕ I, (2 * (⌈H a⌉₊ : ℝ) + 1) := by
    dsimp [box] at hc
    simp only [Fintype.card_piFinset, card_centeredIntegerBox] at hc
    exact_mod_cast hc
  calc
    _ ≤ ∏ a, ∏ _i : Unit ⊕ I, (2 * (⌈H a⌉₊ : ℝ) + 1) := hc'
    _ ≤ ∏ a, ∏ _i : Unit ⊕ I, (5 * H a) := by
      apply Finset.prod_le_prod₀
      · intro a _
        exact Finset.prod_nonneg (fun _ _ => by positivity)
      · intro a _
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro i _
        have hb := Nat.ceil_lt_add_one (show 0 ≤ H a by linarith [hH a])
        linarith [hH a]
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rw [← pow_mul, Nat.mul_comm]

theorem spatialGrid_error_le {A I : Type*} [Fintype A] [Fintype I]
    (H : A → ℝ) (hH : ∀ a, 1 ≤ H a)
    (t : Finset (A → (Unit ⊕ I) → ℤ))
    (ht : ∀ v ∈ t, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ) / H a| ≤ 1)
    {E : ℝ} (hE : 0 ≤ E) :
    E / (∏ a, ∏ _i : Unit ⊕ I, H a) * t.card ≤
      5^(Fintype.card A * Fintype.card (Unit ⊕ I)) * E := by
  have hpos : 0 < ∏ a, ∏ _i : Unit ⊕ I, H a :=
    Finset.prod_pos (fun a _ => Finset.prod_pos (fun _ _ => lt_of_lt_of_le zero_lt_one (hH a)))
  have hc := mul_le_mul_of_nonneg_left (spatialGrid_card_le H hH t ht)
    (div_nonneg hE hpos.le)
  calc
    _ ≤ E / (∏ a, ∏ _i : Unit ⊕ I, H a) *
        (5^(Fintype.card A * Fintype.card (Unit ⊕ I)) *
          (∏ a, ∏ _i : Unit ⊕ I, H a)) := hc
    _ = _ := by field_simp [hpos.ne']

end Erdos3

end

end OAI
