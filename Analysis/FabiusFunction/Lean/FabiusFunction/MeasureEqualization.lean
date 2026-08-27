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

/-- The equalizer step function is integrable on any restricted
measure (each cell has finite mass). -/
theorem integrable_equalizer (μ : Measure ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hfin : ∀ i, i < n → μ (Set.Ioc (x i) (x (i + 1))) ≠ ⊤)
    (A : Set ℝ) :
    Integrable (fun t => ∑ i ∈ Finset.range n,
      Set.indicator (Set.Ioc (x i) (x (i + 1)))
        (fun _ => (x (i + 1) - x i) /
          μ.real (Set.Ioc (x i) (x (i + 1)))) t)
      (μ.restrict A) := by
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  rw [integrable_indicator_iff measurableSet_Ioc]
  have hle : (μ.restrict A) (Set.Ioc (x i) (x (i + 1))) ≤
      μ (Set.Ioc (x i) (x (i + 1))) := Measure.restrict_le_self _
  exact integrableOn_const
    (hs := (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr
      (hfin i (Finset.mem_range.mp hi)))).ne)

/-- The equalizer step function is nonnegative wherever the nodes are
monotone. -/
theorem equalizer_nonneg (μ : Measure ℝ) (x : ℕ → ℝ)
    (hmono : Monotone x) (n : ℕ) (t : ℝ) :
    0 ≤ ∑ i ∈ Finset.range n,
      Set.indicator (Set.Ioc (x i) (x (i + 1)))
        (fun _ => (x (i + 1) - x i) /
          μ.real (Set.Ioc (x i) (x (i + 1)))) t := by
  apply Finset.sum_nonneg
  intro i _
  apply Set.indicator_nonneg
  intro y _
  apply div_nonneg
  · exact sub_nonneg.mpr (hmono (Nat.le_succ i))
  · exact ENNReal.toReal_nonneg

/-- **The partial-cell discrepancy bound**: inside the one partially
traversed cell, the flattened CDF differs from linear by at most the
cell length — *"the mesh bounds the possible error in the one
partially traversed cell"*. -/
theorem abs_setIntegral_equalizer_sub_le (μ : Measure ℝ) (x : ℕ → ℝ)
    (hmono : Monotone x) (n : ℕ)
    (hfin : ∀ i, i < n → μ (Set.Ioc (x i) (x (i + 1))) ≠ ⊤)
    (hpos : ∀ i, i < n → μ (Set.Ioc (x i) (x (i + 1))) ≠ 0)
    (j : ℕ) (hj : j + 1 ≤ n) {z : ℝ} (hz1 : x j ≤ z)
    (hz2 : z ≤ x (j + 1)) :
    |(∫ t in Set.Ioc (x 0) z,
      (∑ i ∈ Finset.range n,
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t) ∂μ) - (z - x 0)| ≤
      x (j + 1) - x j := by
  have hlow := setIntegral_equalizer μ x hmono n hfin hpos j
    (le_trans (Nat.le_succ j) hj)
  have hhigh := setIntegral_equalizer μ x hmono n hfin hpos (j + 1) hj
  have hint_top : IntegrableOn (fun t => ∑ i ∈ Finset.range n,
      Set.indicator (Set.Ioc (x i) (x (i + 1)))
        (fun _ => (x (i + 1) - x i) /
          μ.real (Set.Ioc (x i) (x (i + 1)))) t)
      (Set.Ioc (x 0) (x (j + 1))) μ :=
    integrable_equalizer μ x n hfin _
  have hnn : 0 ≤ᵐ[μ.restrict (Set.Ioc (x 0) (x (j + 1)))]
      (fun t => ∑ i ∈ Finset.range n,
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t) :=
    Filter.Eventually.of_forall (equalizer_nonneg μ x hmono n)
  have hm1 : (∫ t in Set.Ioc (x 0) (x j),
      (∑ i ∈ Finset.range n,
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t) ∂μ) ≤
      ∫ t in Set.Ioc (x 0) z,
        (∑ i ∈ Finset.range n,
          Set.indicator (Set.Ioc (x i) (x (i + 1)))
            (fun _ => (x (i + 1) - x i) /
              μ.real (Set.Ioc (x i) (x (i + 1)))) t) ∂μ := by
    apply MeasureTheory.setIntegral_mono_set
      (hint_top.mono_set (Set.Ioc_subset_Ioc_right hz2)) ?_
      ((Set.Ioc_subset_Ioc_right hz1).eventuallyLE)
    exact Filter.Eventually.of_forall (equalizer_nonneg μ x hmono n)
  have hm2 : (∫ t in Set.Ioc (x 0) z,
      (∑ i ∈ Finset.range n,
        Set.indicator (Set.Ioc (x i) (x (i + 1)))
          (fun _ => (x (i + 1) - x i) /
            μ.real (Set.Ioc (x i) (x (i + 1)))) t) ∂μ) ≤
      ∫ t in Set.Ioc (x 0) (x (j + 1)),
        (∑ i ∈ Finset.range n,
          Set.indicator (Set.Ioc (x i) (x (i + 1)))
            (fun _ => (x (i + 1) - x i) /
              μ.real (Set.Ioc (x i) (x (i + 1)))) t) ∂μ := by
    apply MeasureTheory.setIntegral_mono_set hint_top hnn
      ((Set.Ioc_subset_Ioc_right hz2).eventuallyLE)
  rw [hlow] at hm1
  rw [hhigh] at hm2
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Fabius
