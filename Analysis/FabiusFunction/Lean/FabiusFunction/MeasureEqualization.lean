import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fixed-partition mass equalization

The exact-node step of Document 8's flattening lemma
(`lem:flattening`): re-weighting each partition cell `(xᵢ, xᵢ₊₁]` of a
measure `μ` by the ratio `cell length / cell mass` produces a step
multiplier `r` whose weighted measure agrees with Lebesgue length at
**every** node,

`∫_{(x₀, x_j]} r dμ = x_j − x₀`.

Away from the partially traversed cell this is what makes the
flattened CDF exactly linear; combined with the diagonal selection of
`DiagonalSelection` it is the mechanism of the shell-adaptive analytic
gauge that resolves the unrestricted `(Q2)`.

Stated for an arbitrary measure on `ℝ` and arbitrary monotone nodes —
only the traversed cells need finite nonzero mass.

* `setIntegral_equalizer` — the node-exact identity.
-/

set_option autoImplicit false

open MeasureTheory Set Finset

namespace Fabius

/-- **Fixed-partition mass equalization**: with cell multipliers
`cᵢ = (xᵢ₊₁ − xᵢ)/μ((xᵢ, xᵢ₊₁])`, the step function
`r = ∑ᵢ cᵢ·𝟙_{(xᵢ, xᵢ₊₁]}` satisfies
`∫_{(x₀, x_j]} r dμ = x_j − x₀` for every node index `j ≤ n`. -/
theorem setIntegral_equalizer (μ : Measure ℝ) (x : ℕ → ℝ)
    (hmono : Monotone x) (n : ℕ)
    (hfin : ∀ i, i < n → μ (Set.Ioc (x i) (x (i + 1))) ≠ ⊤)
    (hpos : ∀ i, i < n → μ (Set.Ioc (x i) (x (i + 1))) ≠ 0)
    (j : ℕ) (hj : j ≤ n) :
    ∫ t in Set.Ioc (x 0) (x j),
      (∑ i ∈ Finset.range n,
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t) ∂μ =
      x j - x 0 := by
  have hint : ∀ i ∈ Finset.range n, Integrable
      (fun t => Set.indicator (Set.Ioc (x i) (x (i + 1)))
        (fun _ => (x (i + 1) - x i) /
          μ.real (Set.Ioc (x i) (x (i + 1)))) t)
      (μ.restrict (Set.Ioc (x 0) (x j))) := by
    intro i hi
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hle : (μ.restrict (Set.Ioc (x 0) (x j)))
        (Set.Ioc (x i) (x (i + 1))) ≤ μ (Set.Ioc (x i) (x (i + 1))) := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      exact measure_mono Set.inter_subset_left
    exact integrableOn_const
      (hs := (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr
        (hfin i (Finset.mem_range.mp hi)))).ne)
  rw [MeasureTheory.integral_finsetSum _ hint]
  have hterm : ∀ i ∈ Finset.range n,
      (∫ t in Set.Ioc (x 0) (x j),
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t ∂μ) =
      if i < j then x (i + 1) - x i else 0 := by
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Ioc]
    have hres : (μ.restrict (Set.Ioc (x 0) (x j))).real
        (Set.Ioc (x i) (x (i + 1))) =
        (μ (Set.Ioc (x i) (x (i + 1)) ∩ Set.Ioc (x 0) (x j))).toReal := by
      rw [measureReal_def, Measure.restrict_apply measurableSet_Ioc]
    rcases lt_or_ge i j with hij | hij
    · have hsub : Set.Ioc (x i) (x (i + 1)) ∩ Set.Ioc (x 0) (x j) =
          Set.Ioc (x i) (x (i + 1)) :=
        Set.inter_eq_self_of_subset_left
          (Set.Ioc_subset_Ioc (hmono (Nat.zero_le i))
            (hmono (Nat.succ_le_of_lt hij)))
      rw [if_pos hij, hres, hsub, smul_eq_mul]
      have hne : (μ (Set.Ioc (x i) (x (i + 1)))).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr
          ⟨hpos i hin, hfin i hin⟩
      rw [measureReal_def]
      field_simp
    · have hempty : Set.Ioc (x i) (x (i + 1)) ∩ Set.Ioc (x 0) (x j) =
          (∅ : Set ℝ) := by
        rw [Set.Ioc_inter_Ioc]
        apply Set.Ioc_eq_empty
        rw [not_lt]
        calc min (x (i + 1)) (x j) ≤ x j := min_le_right _ _
          _ ≤ x i := hmono hij
          _ ≤ max (x i) (x 0) := le_max_left _ _
      rw [if_neg (not_lt.mpr hij), hres, hempty]
      simp
  have hsum : ∑ i ∈ Finset.range n,
      (∫ t in Set.Ioc (x 0) (x j),
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t ∂μ) =
      ∑ i ∈ Finset.range n, if i < j then x (i + 1) - x i else 0 :=
    Finset.sum_congr rfl hterm
  rw [hsum]
  have htrim : ∑ i ∈ Finset.range n,
      (if i < j then x (i + 1) - x i else 0) =
      ∑ i ∈ Finset.range j,
        (if i < j then x (i + 1) - x i else 0) :=
    (Finset.sum_subset (Finset.range_subset_range.mpr hj)
      (fun i _ hnot => by
        rw [if_neg]
        exact fun hlt => hnot (Finset.mem_range.mpr hlt))).symm
  rw [htrim]
  have hval : ∑ i ∈ Finset.range j,
      (if i < j then x (i + 1) - x i else 0) =
      ∑ i ∈ Finset.range j, (x (i + 1) - x i) :=
    Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
  rw [hval]
  exact Finset.sum_range_sub x j

end Fabius
