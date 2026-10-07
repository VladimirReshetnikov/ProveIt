import OAI.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

universe u v

theorem quarter_discrepancy_inverse {gap p q : ℝ}
    (hgap : gap⁻¹ ≤ Real.exp p) (hpq : p + 16 ≤ q) :
    (gap / 4)⁻¹ ≤ Real.exp q := by
  have hfour : (4 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  rw [inv_div, div_eq_mul_inv]
  calc
    4 * gap⁻¹ ≤ 4 * Real.exp p := mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp q := Real.exp_le_exp.mpr hpq

theorem physical_comparison_of_anchored
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (m a J P : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hJ : 0 < J) (hP : 0 < P)
    (lo : σ → ℤ) (N : σ → ℕ) (u z : σ → ℤ) (cost gap δ : ℝ)
    (hcost : cost ≤ base.incomingBudget) (hgap : 0 < gap) (hgapOne : gap ≤ 1)
    (hgapInv : gap⁻¹ ≤ Real.exp base.incomingBudget)
    (hcontained : ∀ i, base.lower i ≤ lo i ∧ lo i + N i ≤ base.lower i + base.sides i)
    (hcomparison : AnchoredChildResidueComparison base.model
      (base.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))).orbit
      cost gap δ lo N (m * a) P u z (fun _ => J)) :
    ∃ c : PhysicalEpochComparison base m (a * P) J gap,
      (∀ i, lo i ≤ c.lower i ∧ c.lower i + c.sides i ≤ lo i + N i) ∧
      (∀ i, δ * (N i : ℝ) / 8 ≤ (c.sides i : ℝ) ∧ (c.sides i : ℝ) ≤ δ * (N i : ℝ) / 2) ∧
      (∀ i, c.anchor i ≡ u i [ZMOD (m * a : ℕ)]) ∧
      (∀ i, c.refined i ≡ z i [ZMOD (m * a * J : ℕ)]) := by
  obtain ⟨lo', N', w, z', U, hsub, hpos, hlength, hwInside, hzInside, hw, hz, hzw,
    _, _, hU, hunit, hUcost, hUgap⟩ := hcomparison
  have hQ : Nat.lcm (m * a) (m * a * P) = m * (a * P) := by
    rw [Nat.lcm_eq_right_iff_dvd.mpr (Nat.dvd_mul_right (m * a) P), Nat.mul_assoc]
  have hphysical := base.fixedMap.scalarAffinePullback_refinement_orbit u w
    (Nat.dvd_lcm_left (m * a) (m * a * P)) hw
  have hUphysical := hU.trans hphysical
  rw [hQ] at hUphysical hzw hUgap
  let c : PhysicalEpochComparison base m (a * P) J gap := {
    selected_pos := hm
    auxiliary_pos := Nat.mul_pos ha hP
    pending_pos := hJ
    lower := lo'
    sides := N'
    sides_pos := hpos
    contained := fun i => ⟨(hcontained i).1.trans (hsub i).1, (hsub i).2.trans (hcontained i).2⟩
    anchor := w
    refined := z'
    anchor_inside := hwInside
    refined_inside := hzInside
    compatible := hzw
    test := U
    orbit := hUphysical
    positive := hunit
    complexity := hUcost.mono hcost
    gap_pos := hgap
    gap_le_one := hgapOne
    gap_inverse := hgapInv
    discrepancy := hUgap }
  exact ⟨c, hsub, hlength, hw, hz⟩

end Erdos3

end

end OAI
