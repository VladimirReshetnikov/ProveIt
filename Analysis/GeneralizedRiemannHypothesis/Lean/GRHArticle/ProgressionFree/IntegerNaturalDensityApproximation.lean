import GRHArticle.ProgressionFree.IntegerRoughTemplateDensity

/-!
# Approximating the extremal natural density by smooth templates

For either convention, the smooth optimum at cutoff `Y` bounds the actual
natural-density supremum from above, and the squarefree correction times
that optimum bounds it from below. The interval has width at most `1/Y`.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

private def templateWeights (integral : Bool) (Y : ℕ) : Set ℝ :=
  {w | ∃ S : Set ℕ, S ⊆ Nat.smoothNumbers (Y+1) ∧ IntegerPrefixAdmissible integral S ∧
    w = ∑' s : S, (s.val : ℝ)⁻¹}

private theorem templateWeights_nonempty (integral : Bool) (Y : ℕ) :
    (templateWeights integral Y).Nonempty :=
  ⟨_, ∅, Set.empty_subset _, by intro a b c ha; exact ha.elim, rfl⟩

/-- Squarefree rough parts can carry any admissible fixed smooth template
at the density prescribed by its reciprocal weight. -/
theorem integerSquarefreeRoughFactor_mul_smoothLower_le_naturalDensitySupremum
    (integral : Bool) (Y : ℕ) :
    integerSquarefreeRoughFactor Y * integerSmoothLowerOptimization integral Y ≤
      integerNaturalDensitySupremum integral := by
  let Q := integerSquarefreeRoughNumbers Y
  let d := integerSmoothDensityFactor Y * integerSquarefreeRoughFactor Y
  let b := integerNaturalDensitySupremum integral
  have hQ : Q ⊆ integerRoughNumbers Y := fun _ hr ↦ hr.1
  have hl (w : ℝ) (hw : w ∈ templateWeights integral Y) : d*w ≤ b := by
    obtain ⟨S,hS,ha,rfl⟩ := hw
    apply le_integerNaturalDensitySupremum (A := integerRoughTemplateProducts Q S)
    · rintro ⟨r,s,hr,hs,he⟩
      exact (mul_ne_zero (hQ hr).1 (Nat.ne_zero_of_mem_smoothNumbers (hS hs))) he.symm
    · exact integerRoughTemplate_admissible integral Y Q (fun _ ↦ S) hQ (fun _ h ↦ h.2)
        (fun _ _ ↦ hS) (fun _ _ ↦ ha)
    · exact hasNaturalDensity_integerRoughTemplateProducts hQ hS (hasNaturalDensity_integerSquarefreeRoughNumbers Y)
  have h₀ : 0 ≤ d := mul_nonneg (integerSmoothDensityFactor_pos Y).le
    (integerSquarefreeRoughFactor_mem_unitInterval Y).1
  rw [integerSmoothLowerOptimization, ← mul_assoc, mul_comm (integerSquarefreeRoughFactor Y)]
  change d * sSup (templateWeights integral Y) ≤ b
  rcases h₀.eq_or_lt with hd | hd
  · obtain ⟨w,hw⟩ := templateWeights_nonempty integral Y
    simpa only [← hd, zero_mul] using hl w hw
  · rw [mul_comm, ← le_div_iff₀ hd]
    exact csSup_le (templateWeights_nonempty integral Y) (fun w hw ↦
      (le_div_iff₀ hd).mpr ((mul_comm w d).trans_le (hl w hw)))

theorem integerSmoothLowerOptimization_le_one (integral : Bool) (Y : ℕ) :
    integerSmoothLowerOptimization integral Y ≤ 1 := by
  have h : sSup (templateWeights integral Y) ≤ (integerSmoothDensityFactor Y)⁻¹ := by
    apply csSup_le (templateWeights_nonempty integral Y)
    rintro _ ⟨S,hS,_,rfl⟩
    exact smoothSubset_reciprocal_le hS
  exact (mul_le_mul_of_nonneg_left h (integerSmoothDensityFactor_pos Y).le).trans_eq
    (mul_inv_cancel₀ (integerSmoothDensityFactor_pos Y).ne')

/-- The exact smooth optimum overestimates the extremal natural density by
at most the actual sum of the omitted prime squares. -/
theorem integerSmoothLowerOptimization_error (integral : Bool) (Y : ℕ) :
    integerSmoothLowerOptimization integral Y - integerNaturalDensitySupremum integral ∈
      Set.Icc 0 (integerPrimeSquareTail Y) := by
  refine ⟨sub_nonneg.mpr (integerNaturalDensitySupremum_le_smoothLower integral Y), ?_⟩
  have hl := integerSquarefreeRoughFactor_mul_smoothLower_le_naturalDensitySupremum integral Y
  have hb := integerSmoothLowerOptimization_le_one integral Y
  have hv := (integerSquarefreeRoughFactor_mem_unitInterval Y).2
  have hm := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hv)
  have ht := one_sub_integerSquarefreeRoughFactor_le_primeSquareTail Y
  linarith only [hl,hm,ht]

/-- Both actual natural-density suprema are limits of the fixed smooth optimizations. -/
theorem tendsto_integerSmoothLowerOptimization (integral : Bool) :
    Tendsto (integerSmoothLowerOptimization integral) atTop (𝓝 (integerNaturalDensitySupremum integral)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun Y : ℕ ↦ integerNaturalDensitySupremum integral + 1/(Y:ℝ)) atTop _ from
      (by simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))))
  · exact Eventually.of_forall (integerNaturalDensitySupremum_le_smoothLower integral)
  · filter_upwards [eventually_gt_atTop 0] with Y hY
    have h := (integerSmoothLowerOptimization_error integral Y).2.trans (integerPrimeSquareTail_le_reciprocal hY)
    linarith

end GRHArticle.ProgressionFree
