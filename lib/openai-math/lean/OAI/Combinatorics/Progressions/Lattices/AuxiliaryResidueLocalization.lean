import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
import OAI.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_auxiliary_residue_piece {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (M d J : I → ℕ) (hM : ∀ i, 0 < M i) (hd : ∀ i, 0 < d i) (hJ : ∀ i, 0 < J i)
    (u w : I → ℤ) (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)])
    (hcop : ∀ i, (M i * d i).Coprime (J i)) {ε : ℝ} (hε : ε < 1 / 2)
    (hsmall : (∑ i, (Nat.lcm (M i) (d i) * J i : ℕ) / (H i : ℝ)) ≤ ε)
    (f : IntegerResidueBox a (fun i => a i + N i) (fun i => (M i : ℤ)) u → ℂ)
    (g : IntegerResidueBox a (fun i => a i + N i) (fun i => (M i * J i : ℕ)) w → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) :
    let P := comparableBoxPartitions N H hH hHN
    ∃ k : AuxiliaryBoxLabels P M d u,
      0 < (partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k).card ∧
      0 < (partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k).card ∧
      ‖(𝔼 x, f x) - (𝔼 x, g x)‖ - 8 * ε ≤
        ‖(𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k, f x) -
          (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k, g x)‖ := by
  intro P
  let := auxiliaryBoxLabels_nonempty P (comparableBoxPartitions_nonempty N H hH hHN) M d hd u
  have hstep : ∀ i k, (P i).step k = 1 := comparableBoxPartitions_step N H hH hHN
  have hpos : ∀ i k, 0 < (P i).length k := fun i k =>
    (hH i).trans_le (comparableBoxPartitions_length N H hH hHN i k).1
  let lo : AuxiliaryBoxLabels P M d u → I → ℤ :=
    fun k i => intervalCellLower (a i) (P i) (k i).1
  let hi : AuxiliaryBoxLabels P M d u → I → ℤ :=
    fun k i => intervalCellUpper (a i) (P i) (k i).1
  let R : I → ℤ := fun i => Nat.lcm (M i) (d i)
  let S : I → ℤ := fun i => (Nat.lcm (M i) (d i) * J i : ℕ)
  let v : AuxiliaryBoxLabels P M d u → I → ℤ := fun k i => (k i).2.baseValue
  let z : AuxiliaryBoxLabels P M d u → I → ℤ := fun k i => (k i).2.refinedValue (hcop i) (w i)
  have hL : ∀ i, 0 < Nat.lcm (M i) (d i) := fun i =>
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hM i).ne' (hd i).ne')
  have hRpos : ∀ i, 0 < R i := by
    intro i
    dsimp only [R]
    exact_mod_cast hL i
  have hSpos : ∀ i, 0 < S i := by
    intro i
    dsimp only [S]
    exact_mod_cast Nat.mul_pos (hL i) (hJ i)
  have hsmallS : (∑ i, (S i : ℝ) / (H i : ℝ)) ≤ ε := by
    simpa only [S, Int.cast_natCast] using hsmall
  have hsmallR : (∑ i, (R i : ℝ) / (H i : ℝ)) ≤ ε := by
    apply le_trans (Finset.sum_le_sum fun i _ => ?_) hsmallS
    apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have hle : Nat.lcm (M i) (d i) ≤ Nat.lcm (M i) (d i) * J i := by
      nlinarith [hJ i]
    dsimp only [R, S]
    exact_mod_cast hle
  have hbox : ∀ k i, lo k i < hi k i := by
    intro k i
    apply sub_pos.mp
    change 0 < intervalCellUpper (a i) (P i) (k i).1 - intervalCellLower (a i) (P i) (k i).1
    rw [intervalCell_width]
    exact_mod_cast hpos i (k i).1
  have hR : ∀ k, (∑ i, (R i : ℝ) / ((hi k i - lo k i : ℤ) : ℝ)) ≤ ε :=
    fun k => (comparableBoxPartitions_ratio_le a N H hH hHN R (fun i => (hRpos i).le)
      (fun i => (k i).1)).trans hsmallR
  have hS : ∀ k, (∑ i, (S i : ℝ) / ((hi k i - lo k i : ℤ) : ℝ)) ≤ ε :=
    fun k => (comparableBoxPartitions_ratio_le a N H hH hHN S (fun i => (hSpos i).le)
      (fun i => (k i).1)).trans hsmallS
  let F : AuxiliaryBoxLabels P M d u → ℂ := fun k =>
    𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k, f x
  let G : AuxiliaryBoxLabels P M d u → ℂ := fun k =>
    𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k, g x
  have hG : ∀ k, ‖G k‖ ≤ 1 := by
    intro k
    let A := partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k
    change ‖𝔼 x ∈ A, g x‖ ≤ 1
    by_cases hA : A.Nonempty
    · apply (RCLike.norm_expect_le (K := ℂ)).trans
      exact (Finset.expect_le_expect (fun x _ => hg x)).trans_eq (Finset.expect_const hA 1)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hA
      simp only [he, Finset.expect_empty, norm_zero, zero_le_one]
  obtain ⟨k, hkr, hks, hgap⟩ := exists_rectangular_residue_piece_discrepancy
    lo hi R S v z hbox hRpos hSpos hε hR hS F G hG
  have hmR := boxAuxiliaryCell_mixture a N P hstep hpos M d hd u (fun i => (M i : ℤ)) u
    (fun _ _ hx => hx) R v (fun k i => (k i).2.baseConstraint_iff) f
  have hmS := boxAuxiliaryCell_mixture a N P hstep hpos M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i)) S z
    (fun k i => (k i).2.refinedConstraint_iff (hcop i) (w i) (hw i)) g
  simp only [div_mul_eq_mul_div, ← Finset.sum_div] at hmR hmS
  dsimp only [F, G, lo, hi, baseAuxiliaryBoxCell, refinedAuxiliaryBoxCell] at hgap
  rw [← hmR, ← hmS] at hgap
  refine ⟨k, ?_, ?_, hgap⟩
  · rw [baseAuxiliaryBoxCell_card a N P hstep hpos M d hd u]
    exact Nat.cast_pos.mp hkr
  · rw [refinedAuxiliaryBoxCell_card a N P hstep hpos M d J hd u w hw hcop]
    exact Nat.cast_pos.mp hks

end Erdos3

end

end OAI
