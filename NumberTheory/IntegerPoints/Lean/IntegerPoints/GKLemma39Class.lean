import IntegerPoints.GKLemma39

/-!
# Graham--Kolesnik, Lemma 3.9: the class-form corollary

Lemma 3.9 gives the inverse phase derivative estimate on the full derivative interval
`[f'(b), f'(a)]`.  The remark following the lemma restricts that estimate to its intersection
with a dyadic interval `[J, 2J]`.  This module packages the restriction as membership in the
Graham--Kolesnik class

`F(J, P, 1 / s, y ^ (1 / s), C * eps)`.

The only geometric point requiring more than interval arithmetic is positivity of `J`: it
follows from positivity of `f'(b)` and the hypothesis `f'(b) ≤ J`.  Hence the restricted lower
endpoint is at most `2J`, so the class interval is correctly contained in `[J, 2J]`.
-/

open Real Finset Set

namespace LeanProofs.IntegerPoints

/-- **Graham--Kolesnik, §3.5, class-form consequence of Lemma 3.9.** -/
theorem gk_lemma39_class_holds : gk_lemma39_class := by
  intro s P hs hP
  obtain ⟨C, hC⟩ := gk_lemma39_holds s P hs hP
  refine ⟨C, ?_⟩
  intro N y eps a b f x phi hN hy heps heps_half hf hab hphi hx hlegendre
    J hJ_lower hJ_upper
  have hestimate := hC N y eps a b f x phi hN hy heps heps_half hf hab
    hphi hx hlegendre
  have hderiv_b_pos : 0 < deriv f b :=
    (GK39.deriv_interval_pos hN hs hy hP heps heps_half hf hab).1
  have hJ_pos : 0 < J := hderiv_b_pos.trans_le hJ_lower
  refine ⟨le_max_right _ _, ?_, min_le_right _ _, hphi, ?_⟩
  · rw [max_eq_right hJ_lower]
    exact le_min hJ_upper (by linarith)
  · intro p hp nu hnu
    have hnu_full : nu ∈ Icc (deriv f b) (deriv f a) := by
      exact ⟨(le_max_left _ _).trans hnu.1,
        hnu.2.trans (min_le_left _ _)⟩
    exact hestimate p hp nu hnu_full

end LeanProofs.IntegerPoints
