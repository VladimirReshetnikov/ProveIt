import Mathlib

namespace OAI

section

namespace Erdos3

open Finset
open scoped BigOperators

theorem exists_regular_point_of_monotone
    (f : ℝ → ℝ) (hf : Monotone f)
    (hgrowth : f (5 / 4) - f (1 / 4) < 5) :
    ∃ x ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 4 : ℝ) (5 / 4),
        |f y - f x| ≤ 60 * |y - x| := by
  classical
  by_contra! hregular
  let Bad : Set (ℝ × ℝ) := {p |
    1 / 4 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 5 / 4 ∧
      60 * (p.2 - p.1) < f p.2 - f p.1}
  let center : (ℝ × ℝ) → ℝ := fun p ↦ (p.1 + p.2) / 2
  let radius : (ℝ × ℝ) → ℝ := fun p ↦ (p.2 - p.1) / 2
  have hradius_pos {p : ℝ × ℝ} (hp : p ∈ Bad) : 0 < radius p := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  have hradius_le (p : ℝ × ℝ) (hp : p ∈ Bad) : radius p ≤ 1 / 2 := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  obtain ⟨u, huBad, huDisjoint, huCover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      Bad center radius (1 / 2) hradius_le 5 (by norm_num)
  have hcentralCover : Set.Icc (1 / 2 : ℝ) 1 ⊆
      ⋃ b : ↥u, Metric.ball (center b.1) (6 * radius b.1) := by
    intro x hx
    obtain ⟨y, hybuf, hxy⟩ := hregular x hx
    let p : ℝ × ℝ := (min x y, max x y)
    have hpbuf : p ∈ Bad := by
      dsimp [Bad, p]
      have hxbuf : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
        constructor <;> linarith [hx.1, hx.2]
      rcases le_total x y with hle | hle
      · simp only [min_eq_left hle, max_eq_right hle]
        have habs : |f y - f x| = f y - f x :=
          abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hxbuf.1, lt_of_not_ge (fun heq ↦ by
          have : y = x := le_antisymm heq hle
          subst y
          norm_num at hxy), hybuf.2, hxy⟩
      · simp only [min_eq_right hle, max_eq_left hle]
        have habs : |f y - f x| = f x - f y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = x - y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hybuf.1, lt_of_not_ge (fun heq ↦ by
          have : x = y := le_antisymm heq hle
          subst y
          norm_num at hxy), hxbuf.2, hxy⟩
    obtain ⟨b, hbu, hsub⟩ := huCover p hpbuf
    have hxp : x ∈ Metric.closedBall (center p) (radius p) := by
      rw [Real.closedBall_eq_Icc]
      dsimp [center, radius, p]
      constructor <;> rcases le_total x y with hle | hle <;>
        simp [hle] <;> linarith
    have hxb : x ∈ Metric.closedBall (center b) (5 * radius b) := hsub hxp
    rw [Metric.mem_closedBall] at hxb
    rw [Set.mem_iUnion]
    refine ⟨⟨b, hbu⟩, ?_⟩
    rw [Metric.mem_ball]
    have hbr : 0 < radius b := hradius_pos (huBad hbu)
    linarith
  obtain ⟨v, hvCover⟩ := isCompact_Icc.elim_finite_subcover
    (fun b : ↥u ↦ Metric.ball (center b.1) (6 * radius b.1))
    (fun _ ↦ Metric.isOpen_ball) hcentralCover
  have hv_nonempty : v.Nonempty := by
    by_contra hv
    rw [Finset.not_nonempty_iff_eq_empty] at hv
    simpa [hv] using hvCover (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1 by norm_num)
  have hvolume : (1 / 2 : ℝ) ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
    have hm : MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
        MeasureTheory.volume (⋃ b ∈ v,
          Metric.ball (center b.1) (6 * radius b.1)) :=
      MeasureTheory.measure_mono hvCover
    have hright : 0 ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro b hb
      have := hradius_pos (huBad b.2)
      dsimp [radius] at this
      linarith
    rw [← ENNReal.ofReal_le_ofReal_iff hright]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) =
        MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) := by
      rw [Real.volume_Icc]
      norm_num
    rw [hhalf]
    calc
      MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
          MeasureTheory.volume (⋃ b ∈ v,
            Metric.ball (center b.1) (6 * radius b.1)) := hm
      _ ≤ ∑ b ∈ v, MeasureTheory.volume
          (Metric.ball (center b.1) (6 * radius b.1)) :=
        MeasureTheory.measure_biUnion_finset_le v _
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := by
        simp only [Real.volume_ball]
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [radius]
          calc
            ∑ b ∈ v, 2 * (6 * ((b.1.2 - b.1.1) / 2)) =
                ∑ b ∈ v, 6 * (b.1.2 - b.1.1) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
            _ = 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
              rw [Finset.mul_sum]
        · intro b hb
          have := hradius_pos (huBad b.2)
          dsimp [radius] at this
          positivity
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := rfl
  let e : ↥u ↪ (ℝ × ℝ) := ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset (ℝ × ℝ) := v.map e
  have hball (p : ℝ × ℝ) :
      Metric.closedBall (center p) (radius p) = Set.Icc p.1 p.2 := by
    rw [Real.closedBall_eq_Icc]
    dsimp [center, radius]
    congr <;> ring
  have hF_bounds : ∀ ⦃z⦄, z ∈ F →
      (1 / 4 : ℝ) ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 5 / 4 := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    have hbad := huBad b.2
    dsimp [Bad] at hbad
    exact ⟨hbad.1, hbad.2.1.le, hbad.2.2.1⟩
  have hF_disjoint : (SetLike.coe F).PairwiseDisjoint
      (fun z ↦ Set.Icc z.1 z.2) := by
    intro z hz w hw hzw
    obtain ⟨bz, hbz, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨bw, hbw, rfl⟩ := Finset.mem_map.mp hw
    have hne : (bz : ℝ × ℝ) ≠ bw := by
      simpa [e] using hzw
    have hd := huDisjoint bz.2 bw.2 hne
    change Disjoint (Metric.closedBall (center bz) (radius bz))
      (Metric.closedBall (center bw) (radius bw)) at hd
    rw [hball, hball] at hd
    simpa [e] using hd
  have hsum_le : ∑ z ∈ F, (f z.2 - f z.1) ≤ f (5 / 4) - f (1 / 4) := by
    have htel := F.sum_intervalGapsWithin_add_sum_eq_sub rfl
      (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) f
    calc
      ∑ z ∈ F, (f z.2 - f z.1) ≤ _ := by
        rw [le_add_iff_nonneg_left]
        apply Finset.sum_nonneg
        intro i hi
        apply sub_nonneg.mpr
        apply hf
        exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
          hF_bounds hF_disjoint
      _ = f (5 / 4) - f (1 / 4) := htel
  have hbad_sum : 60 * ∑ b ∈ v, (b.1.2 - b.1.1) <
      ∑ z ∈ F, (f z.2 - f z.1) := by
    rw [Finset.sum_map]
    simp only [e, Function.Embedding.coeFn_mk]
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hv_nonempty
      (fun b hb ↦ (huBad b.2).2.2.2)
  linarith

end Erdos3

end

end OAI
