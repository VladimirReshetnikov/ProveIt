import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_split_coordinate {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G]
    (i : I) (F : (I → G) → ℝ) :
    (𝔼 t, F t) = 𝔼 z : ({j : I // j ≠ i} → G),
      𝔼 a : G, F ((Equiv.funSplitAt i G).symm (a, z)) := by
  calc
    _ = 𝔼 u : G × ({j : I // j ≠ i} → G), F ((Equiv.funSplitAt i G).symm u) := by
      apply Fintype.expect_equiv (Equiv.funSplitAt i G)
      intro t
      rw [Equiv.symm_apply_apply]
    _ = 𝔼 a : G, 𝔼 z : ({j : I // j ≠ i} → G), F ((Equiv.funSplitAt i G).symm (a, z)) := by
      exact Finset.expect_product' (Finset.univ : Finset G)
        (Finset.univ : Finset ({j : I // j ≠ i} → G))
        (fun a z => F ((Equiv.funSplitAt i G).symm (a, z)))
    _ = _ := Finset.expect_comm _ _ _

theorem expect_neg_membership {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (E : Finset G) :
    (𝔼 a : G, if -a ∈ E then (1 : ℝ) else 0) = (E.card : ℝ) / Fintype.card G := by
  classical
  let e : G ≃ G := ⟨Neg.neg, Neg.neg, neg_neg, neg_neg⟩
  calc
    _ = 𝔼 a : G, if a ∈ E then (1 : ℝ) else 0 := by
      apply Fintype.expect_equiv e
      intro a
      rfl
    _ = _ := by simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem]

theorem conditional_neg_coordinate_bad_mean {I G : Type*}
    [Fintype I] [DecidableEq I] [AddGroup G] [Fintype G] [DecidableEq G]
    (i : I) (E : (I → G) → Finset G) {delta : ℝ}
    (hE : ∀ t, ((E t).card : ℝ) ≤ delta * (Fintype.card G : ℝ))
    (hindependent : ∀ t a, E (Function.update t i a) = E t) :
    (𝔼 t : I → G, if -(t i) ∈ E t then (1 : ℝ) else 0) ≤ delta := by
  classical
  rw [expect_split_coordinate i]
  apply (Finset.expect_le_expect (fun z _ => ?_)).trans_eq (Finset.expect_const Finset.univ_nonempty delta)
  let e := Equiv.funSplitAt i G
  have hupdate (a : G) : Function.update (e.symm (0, z)) i a = e.symm (a, z) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have heq (a : G) : E (e.symm (a, z)) = E (e.symm (0, z)) := by
    rw [← hupdate a]
    exact hindependent _ _
  have hval (a : G) : e.symm (a, z) i = a := by
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  change (𝔼 a : G, if -(e.symm (a, z) i) ∈ E (e.symm (a, z)) then (1 : ℝ) else 0) ≤ delta
  simp_rw [hval, heq]
  rw [expect_neg_membership]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
  exact hE _

theorem finite_union_indicator_mean_le {I X : Type*} [Fintype I] [Fintype X]
    (bad : I → X → Prop) [∀ i, DecidablePred (bad i)] {delta : ℝ}
    (hbad : ∀ i, (𝔼 x, if bad i x then (1 : ℝ) else 0) ≤ delta) :
    (𝔼 x, if ∃ i, bad i x then (1 : ℝ) else 0) ≤ (Fintype.card I : ℝ) * delta := by
  classical
  have hpoint (x : X) : (if ∃ i, bad i x then (1 : ℝ) else 0) ≤
      ∑ i, if bad i x then (1 : ℝ) else 0 := by
    split_ifs with hx
    · obtain ⟨i, hi⟩ := hx
      have h := Finset.single_le_sum (f := fun i => if bad i x then (1 : ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [hi, ite_true] using h
    · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  calc
    _ ≤ 𝔼 x, ∑ i, if bad i x then (1 : ℝ) else 0 := Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ i, 𝔼 x, if bad i x then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _i : I, delta := Finset.sum_le_sum (fun i _ => hbad i)
    _ = _ := by simp

end Erdos3

end

end OAI
