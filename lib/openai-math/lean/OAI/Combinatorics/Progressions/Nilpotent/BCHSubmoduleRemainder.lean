import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightBracketList_mem_submodule (K W : Submodule ℚ L)
    (hbracket : ∀ x ∈ W, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (f : X → L) (hf : ∀ x, f x ∈ K) (xs : List X) (a : L) (ha : a ∈ W) :
    rightBracketList f xs a ∈ W := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih ⁅a, f x⁆ (hbracket a ha (f x) (hf x))

theorem dynkinWord_mem_submodule_of_nonlinear (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (f : X → L) (hf : ∀ x, f x ∈ K) (w : FreeSemigroup X) (hw : w.tail ≠ []) :
    dynkinWord f w ∈ W := by
  unfold dynkinWord
  cases ht : w.tail with
  | nil => exact False.elim (hw ht)
  | cons x xs =>
    exact rightBracketList_mem_submodule K W
      (fun a ha b hb => hbracket a (hWK ha) b hb) f hf xs ⁅f w.head, f x⁆
        (hbracket _ (hf _) _ (hf _))

theorem lieBCH_sub_add_mem_submodule {s : ℕ} (hs : 1 ≤ s)
    (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (a b : L) (ha : a ∈ K) (hb : b ∈ K) :
    lieBCH s a b - (a + b) ∈ W := by
  classical
  rw [lieBCH_eq_add_nonlinear_sum hs, add_sub_cancel_left]
  apply Submodule.sum_mem
  intro w hw
  apply W.smul_mem
  apply dynkinWord_mem_submodule_of_nonlinear K W hWK hbracket ![a, b]
  · intro i
    fin_cases i
    · exact ha
    · exact hb
  · exact (Finset.mem_filter.mp hw).2

theorem lieBCH_triple_sub_sum_mem_submodule {s : ℕ} (hs : 1 ≤ s)
    (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (a b c : L) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    lieBCH s (lieBCH s a b) c - (a + b + c) ∈ W := by
  have hab := lieBCH_sub_add_mem_submodule hs K W hWK hbracket a b ha hb
  have habK : lieBCH s a b ∈ K := by
    simpa only [sub_add_cancel] using K.add_mem (hWK hab) (K.add_mem ha hb)
  have habc := lieBCH_sub_add_mem_submodule hs K W hWK hbracket (lieBCH s a b) c habK hc
  convert W.add_mem habc hab using 1
  abel

end Erdos3

end

end OAI
