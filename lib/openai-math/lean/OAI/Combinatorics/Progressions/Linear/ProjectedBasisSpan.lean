import OAI.Combinatorics.Progressions.Geometry.MinkowskiSecondBoxGlue

namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem mem_first_span_of_projection_zero {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ))
    (q : Basis (Fin n) ℝ (Fin n → ℝ))
    (π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hzero : π (b 0) = 0) (htail : ∀ j, π (b j.succ) = q j)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ span ℤ (Set.range b)) (hπx : π x = 0) :
    x ∈ span ℤ ({b 0} : Set (Fin (n + 1) → ℝ)) := by
  classical
  rw [mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  have hp : ∑ j : Fin n, c j.succ • q j = 0 := by
    rw [map_sum, Fin.sum_univ_succ] at hπx
    simpa only [map_zsmul, hzero, htail, smul_zero, zero_add] using hπx
  have hc : ∀ j : Fin n, c j.succ = 0 :=
    Fintype.linearIndependent_iff.mp (q.linearIndependent.restrict_scalars' ℤ) _ hp
  rw [Fin.sum_univ_succ]
  simp only [hc, zero_smul, Finset.sum_const_zero, add_zero]
  exact smul_mem _ _ (subset_span (Set.mem_singleton _))

theorem span_fin_cons_of_projected_span {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ))
    (q : Basis (Fin n) ℝ (Fin n → ℝ))
    (π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hzero : π (b 0) = 0) (htail : ∀ j, π (b j.succ) = q j)
    (w : Fin n → Fin (n + 1) → ℝ)
    (hw : ∀ j, w j ∈ span ℤ (Set.range b))
    (hspan : span ℤ (Set.range (fun j => π (w j))) = span ℤ (Set.range q)) :
    span ℤ (Set.range (Fin.cons (b 0) w)) = span ℤ (Set.range b) := by
  classical
  let L := span ℤ (Set.range b)
  let S := span ℤ (Set.range (Fin.cons (b 0) w))
  have hfirst : b 0 ∈ S := subset_span ⟨0, rfl⟩
  have hwm : ∀ j, w j ∈ S := fun j => subset_span ⟨j.succ, rfl⟩
  have hsmall : span ℤ ({b 0} : Set (Fin (n + 1) → ℝ)) ≤ S := by
    exact span_le.mpr (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hfirst)
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Fin.cases (subset_span (Set.mem_range_self 0)) hw i
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases hfirst (fun k => ?_) i
    change b k.succ ∈ S
    have hk : q k ∈ span ℤ (Set.range (fun j => π (w j))) := by
      rw [hspan]
      exact subset_span (Set.mem_range_self k)
    rw [mem_span_range_iff_exists_fun] at hk
    obtain ⟨c, hc⟩ := hk
    let y := ∑ j, c j • w j
    have hyL : y ∈ L := sum_mem (fun j _ => smul_mem _ _ (hw j))
    have hyS : y ∈ S := sum_mem (fun j _ => smul_mem _ _ (hwm j))
    have hdiff : b k.succ - y ∈ L :=
      sub_mem (subset_span (Set.mem_range_self k.succ)) hyL
    have hπdiff : π (b k.succ - y) = 0 := by
      rw [map_sub, htail]
      change q k - π (∑ j, c j • w j) = 0
      rw [map_sum]
      simp only [map_zsmul, hc, sub_self]
    have hm := mem_first_span_of_projection_zero b q π hzero htail hdiff hπdiff
    have hadd := S.add_mem (hsmall hm) hyS
    simpa only [sub_add_cancel] using hadd

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
