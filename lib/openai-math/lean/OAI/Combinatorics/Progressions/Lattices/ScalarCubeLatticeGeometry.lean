import OAI.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_formula {I : Type*} [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) (t : Finset I) :
    scalarCubeValue x t = x none + ∑ i ∈ t, x (some i) := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

theorem scalarCubeIndicator_disagreement {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (he : ‖y-x‖ ≤ δ)
    (hne : scalarCubeIndicator I y ≠ scalarCubeIndicator I x) :
    ∃ i : Bool × Finset I, x ∈ scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ) := by
  have hv (t : Finset I) := scalarCubeValue_sub_bound y x hδ he t
  have hxnorm (hy : y ∈ halfOpenScalarCubeDomain I) : ‖x‖ ≤ 2 := by
    have ht : ‖x‖ ≤ ‖y-x‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖-(y-x)+y‖ := by congr 1; abel
        _ ≤ ‖-(y-x)‖ + ‖y‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    linarith [halfOpenScalarCubeDomain_norm_le hy]
  by_cases hx : x ∈ halfOpenScalarCubeDomain I
  · have hy : y ∉ halfOpenScalarCubeDomain I := by
      intro hy
      exact hne (by simp only [scalarCubeIndicator, hx, hy, ite_true])
    obtain ⟨t, ht⟩ := not_forall.mp hy
    have hbox : x ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (halfOpenScalarCubeDomain_norm_le hx).trans (by norm_num : (1 : ℝ) ≤ 2)
    have hxval := hx t
    have hdiff := abs_le.mp (hv t)
    by_cases hlo : scalarCubeValue y t < 0
    · refine ⟨(false,t), hbox, ?_⟩
      change |scalarCubeValue x t| ≤ _
      rw [abs_of_nonneg hxval.1]
      linarith [hxval.1, hxval.2, hdiff.1, hdiff.2]
    · have hhi : 1 ≤ scalarCubeValue y t := by
        by_contra! hn
        exact ht ⟨le_of_not_gt hlo, hn⟩
      refine ⟨(true,t), hbox, ?_⟩
      change |1-scalarCubeValue x t| ≤ _
      rw [abs_of_nonneg (by linarith [hxval.2])]
      linarith [hxval.1, hxval.2, hdiff.1, hdiff.2]
  · have hy : y ∈ halfOpenScalarCubeDomain I := by
      by_contra hy
      exact hne (by simp only [scalarCubeIndicator, hx, hy, ite_false])
    obtain ⟨t, ht⟩ := not_forall.mp hx
    have hbox : x ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxnorm hy
    have hyval := hy t
    have hdiff := abs_le.mp (hv t)
    by_cases hlo : scalarCubeValue x t < 0
    · refine ⟨(false,t), hbox, ?_⟩
      change |scalarCubeValue x t| ≤ _
      rw [abs_of_neg hlo]
      linarith [hyval.1, hyval.2, hdiff.1, hdiff.2]
    · have hhi : 1 ≤ scalarCubeValue x t := by
        by_contra! hn
        exact ht ⟨le_of_not_gt hlo, hn⟩
      refine ⟨(true,t), hbox, ?_⟩
      change |1-scalarCubeValue x t| ≤ _
      rw [abs_of_nonpos (by linarith)]
      linarith [hyval.1, hyval.2, hdiff.1, hdiff.2]

end Erdos3

end

end OAI
