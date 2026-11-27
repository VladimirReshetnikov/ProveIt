import GRHArticle.ProgressionFree.IntegerNaturalDensityComputability

/-!
# Finite templates approaching the extremal natural density

The finite search provides actual admissible templates. Placing these on
squarefree rough parts gives admissible integer sets of known natural
densities tending to the supremum for the chosen ratio convention.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Finset

private theorem exists_finiteTemplateApprox (integral : Bool) (Y H : ℕ) :
    ∃ A : Finset ℕ, (A : Set ℕ) ⊆ Nat.smoothNumbers (Y+1) ∧
      IntegerPrefixAdmissible integral (A : Set ℕ) ∧
      (integerFiniteTemplateApprox integral Y H : ℝ) =
        integerSmoothDensityFactor Y * ∑' s : ↥A, (s.val:ℝ)⁻¹ := by
  have hempty : (integerFiniteTemplateCandidates integral Y H).Nonempty :=
    ⟨∅,mem_integerFiniteTemplateCandidates.mpr ⟨empty_subset _, by
      intro a b c ha; exact (Finset.notMem_empty a ha).elim⟩⟩
  obtain ⟨A,hA,hm⟩ := exists_mem_eq_sup' hempty integerTemplateWeightRat
  obtain ⟨hS,ha⟩ := mem_integerFiniteTemplateCandidates.mp hA
  refine ⟨A,fun _ h ↦ (mem_filter.mp (hS h)).2,ha,?_⟩
  rw [integerFiniteTemplateApprox,hm,Rat.cast_mul,cast_integerRoughDensityRat,
    cast_integerTemplateWeightRat,Finset.tsum_subtype A (fun s : ℕ ↦ (s:ℝ)⁻¹)]

private theorem tendsto_dyadic_error :
    Tendsto (fun k : ℕ ↦ (1/2:ℝ)^(k+1)) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).comp
    (tendsto_add_atTop_nat 1)

/-- The executable approximations converge to the requested natural-density supremum. -/
theorem tendsto_integerNaturalDensityApprox (integral : Bool) :
    Tendsto (fun k : ℕ ↦ (integerNaturalDensityApprox integral k : ℝ)) atTop
      (𝓝 (integerNaturalDensitySupremum integral)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [tendsto_dyadic_error.eventually_lt_const hε] with k hk
  rw [Real.dist_eq]
  exact (integerNaturalDensityApprox_error integral k).trans_lt hk

/-- Both conventions admit a sequence of finite smooth templates whose
squarefree rough product sets have natural densities tending to the
unrestricted natural-density supremum. -/
theorem exists_integerNearOptimalFiniteTemplates (integral : Bool) :
    ∃ (Y : ℕ → ℕ) (A : ℕ → Finset ℕ) (e : ℕ → ℝ),
      (∀ j, (A j : Set ℕ) ⊆ Nat.smoothNumbers (Y j+1) ∧
        IntegerPrefixAdmissible integral (A j : Set ℕ) ∧
        HasNaturalDensity (integerRoughTemplateProducts (integerSquarefreeRoughNumbers (Y j)) (A j))
          (e j)) ∧ Tendsto e atTop (𝓝 (integerNaturalDensitySupremum integral)) := by
  let Y (j : ℕ) : ℕ := 2^(j+1)
  choose A hS hA hw using fun j : ℕ ↦
    exists_finiteTemplateApprox integral (Y j) (integerTemplateCutoff (Y j) j)
  let e (j : ℕ) := integerSquarefreeRoughFactor (Y j) * (integerNaturalDensityApprox integral j : ℝ)
  refine ⟨Y,A,e,?_,?_⟩
  · intro j
    refine ⟨hS j,hA j,?_⟩
    have hd := hasNaturalDensity_integerRoughTemplateProducts (fun _ h ↦ h.1) (hS j)
      (hasNaturalDensity_integerSquarefreeRoughNumbers (Y j))
    dsimp only [e,integerNaturalDensityApprox]
    rw [hw j]
    rw [← mul_assoc, mul_comm (integerSquarefreeRoughFactor (Y j)) (integerSmoothDensityFactor (Y j))]
    exact hd
  · have hv : Tendsto (fun j ↦ integerSquarefreeRoughFactor (Y j)) atTop (𝓝 1) := by
      have hl := (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_dyadic_error
      rw [sub_zero] at hl
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds _ (fun j ↦ (integerSquarefreeRoughFactor_mem_unitInterval (Y j)).2)
      intro j
      have h := (one_sub_integerSquarefreeRoughFactor_le_primeSquareTail (Y j)).trans
        (integerPrimeSquareTail_le_reciprocal (Y := Y j) (by dsimp [Y]; positivity))
      have hy : 1/(Y j : ℝ) = (1/2:ℝ)^(j+1) := by simp [Y]
      rw [hy] at h
      linarith
    simpa only [one_mul] using hv.mul (tendsto_integerNaturalDensityApprox integral)

end GRHArticle.ProgressionFree
