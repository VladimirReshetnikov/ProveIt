import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalSourceExistence
import OAI.Combinatorics.Progressions.Geometry.PreparedEarlySpatialWidth
import OAI.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
import OAI.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedSamplerBlockCount (m dim : ℕ) (j : Fin m) : ℕ :=
  let rows := boundedBooleanJetRows (Fin dim) (j.val + 1)
  1 + Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) +
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card))

theorem preparedSamplerBlockCount_positive (m dim : ℕ) (j : Fin m) :
    0 < preparedSamplerBlockCount m dim j := by dsimp only [preparedSamplerBlockCount]; omega

theorem preparedSamplerBlockCount_spectrum (m dim : ℕ) (j : Fin m) :
    let rows := boundedBooleanJetRows (Fin dim) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedSamplerBlockCount m dim j := by dsimp only [preparedSamplerBlockCount]; omega

theorem preparedSamplerBlockCount_jets (m dim : ℕ) (j : Fin m) :
    Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) ≤ preparedSamplerBlockCount m dim j := by
  dsimp only [preparedSamplerBlockCount]
  omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev PreparedSamplerContinuous (j : Fin m) := Fin (L j).rank

noncomputable def preparedSamplerTransverse (j : Fin m) : ℕ :=
  finrank ℝ (euclideanSubspace (L j).space)ᗮ

abbrev PreparedSamplerBlock (dim : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :=
  Fin (preparedSamplerBlockCount m dim a.1)

noncomputable def preparedSamplerDimension (m dim M : ℕ) : ℕ :=
  dim * (dim + 2) + M * m * (∑ j, preparedSamplerBlockCount m dim j) + M + m + 2

theorem preparedSamplerDimension_ge (m dim M : ℕ) : M ≤ preparedSamplerDimension m dim M := by
  unfold preparedSamplerDimension
  omega

theorem preparedSampler_axis_card (j : Fin m) :
    Fintype.card (PreparedSamplerContinuous L j) + preparedSamplerTransverse L j =
      Fintype.card (L j).Coord := by
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, preparedSamplerTransverse] using
    (L j).rank_add_orthogonal_finrank

theorem preparedSampler_variables_card (dim : ℕ) :
    Fintype.card (LayerSamplerVariables (Fin (dim * (dim + 2)))
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (PreparedSamplerBlock L dim)) =
      dim * (dim + 2) + ∑ j : Fin m,
        Fintype.card (L j).Coord * (preparedSamplerBlockCount m dim j * (j.val + 1)) := by
  rw [samplerTupleIndex_card]
  simp only [Fintype.card_fin, LayerSamplerAxis, Fintype.sum_sigma,
    PreparedSamplerBlock, layerSamplerDegree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, Nat.cast_id] using
    congrArg (fun d : ℕ => d * (preparedSamplerBlockCount m dim j * (j.val + 1)))
      (preparedSampler_axis_card L j)

theorem preparedSampler_dimensions (dim : ℕ) {M : ℕ}
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (LayerSamplerVariables (Fin (dim * (dim + 2)))
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (PreparedSamplerBlock L dim)) ≤
        preparedSamplerDimension m dim M ∧
      (∀ j, Fintype.card (PreparedSamplerContinuous L j) ≤ preparedSamplerDimension m dim M) ∧
      (∀ j, preparedSamplerTransverse L j ≤ preparedSamplerDimension m dim M) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [preparedSampler_variables_card]
    have hs : (∑ j : Fin m, Fintype.card (L j).Coord *
        (preparedSamplerBlockCount m dim j * (j.val + 1))) ≤
        M * m * (∑ j, preparedSamplerBlockCount m dim j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ M * (preparedSamplerBlockCount m dim j * m) :=
          Nat.mul_le_mul (hM j) (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt j.isLt))
        _ = _ := by ring
    unfold preparedSamplerDimension
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := preparedSamplerDimension_ge m dim M
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := preparedSamplerDimension_ge m dim M
    omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedCommonBlockCount (m : ℕ) (j : Fin m) : ℕ :=
  ∑ s : Fin (m + 1), preparedSamplerBlockCount m (s.val + 1) j

theorem preparedCommonBlockCount_ge (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    preparedSamplerBlockCount m (s.val + 1) j ≤ preparedCommonBlockCount m j := by
  exact Finset.single_le_sum
    (f := fun r : Fin (m + 1) => preparedSamplerBlockCount m (r.val + 1) j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

theorem preparedCommonBlockCount_positive (m : ℕ) (j : Fin m) :
    0 < preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_positive m 1 j).trans_le (preparedCommonBlockCount_ge m j 0)

theorem preparedCommonBlockCount_spectrum (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    let rows := boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_spectrum m (s.val + 1) j).trans (preparedCommonBlockCount_ge m j s)

theorem preparedCommonBlockCount_jets (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    Fintype.card (BoundedBooleanJet (Fin (s.val + 1)) (j.val + 1)) ≤ preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_jets m (s.val + 1) j).trans (preparedCommonBlockCount_ge m j s)

abbrev PreparedCommonKernel (m : ℕ) := Fin ((m + 1) * (m + 3))

theorem preparedCommonKernel_card (m : ℕ) (s : Fin (m + 1)) :
    (s.val + 1) * ((s.val + 1) + 2) ≤ Fintype.card (PreparedCommonKernel m) := by
  simp only [PreparedCommonKernel, Fintype.card_fin]
  exact Nat.mul_le_mul (by omega) (by omega)

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev PreparedCommonSamplerBlock
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :=
  Fin (preparedCommonBlockCount m a.1)

noncomputable def preparedCommonSamplerDimension (m M : ℕ) : ℕ :=
  (m + 1) * (m + 3) + M * m * (∑ j, preparedCommonBlockCount m j) + M + m + 2

theorem preparedCommonSamplerDimension_ge (m M : ℕ) : M ≤ preparedCommonSamplerDimension m M := by
  unfold preparedCommonSamplerDimension
  omega

theorem preparedCommonSampler_variables_card :
    Fintype.card (LayerSamplerVariables (PreparedCommonKernel m)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (PreparedCommonSamplerBlock L)) =
      (m + 1) * (m + 3) + ∑ j : Fin m,
        Fintype.card (L j).Coord * (preparedCommonBlockCount m j * (j.val + 1)) := by
  rw [samplerTupleIndex_card]
  simp only [PreparedCommonKernel, Fintype.card_fin, LayerSamplerAxis, Fintype.sum_sigma,
    PreparedCommonSamplerBlock, layerSamplerDegree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, Nat.cast_id] using
    congrArg (fun d : ℕ => d * (preparedCommonBlockCount m j * (j.val + 1)))
      (preparedSampler_axis_card L j)

theorem preparedCommonSampler_dimensions {M : ℕ}
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (LayerSamplerVariables (PreparedCommonKernel m)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (PreparedCommonSamplerBlock L)) ≤
        preparedCommonSamplerDimension m M ∧
      (∀ j, Fintype.card (PreparedSamplerContinuous L j) ≤ preparedCommonSamplerDimension m M) ∧
      (∀ j, preparedSamplerTransverse L j ≤ preparedCommonSamplerDimension m M) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [preparedCommonSampler_variables_card]
    have hs : (∑ j : Fin m, Fintype.card (L j).Coord *
        (preparedCommonBlockCount m j * (j.val + 1))) ≤
        M * m * (∑ j, preparedCommonBlockCount m j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ M * (preparedCommonBlockCount m j * m) :=
          Nat.mul_le_mul (hM j) (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt j.isLt))
        _ = _ := by ring
    unfold preparedCommonSamplerDimension
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := preparedCommonSamplerDimension_ge m M
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := preparedCommonSamplerDimension_ge m M
    omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedCommonBlockCountWithCutoff (m d : ℕ) (j : Fin m) : ℕ :=
  ∑ s : Fin (d + 1), preparedSamplerBlockCount m (s.val + 1) j

theorem preparedCommonBlockCountWithCutoff_ge (m d : ℕ) (j : Fin m) (s : Fin (d + 1)) :
    preparedSamplerBlockCount m (s.val + 1) j ≤ preparedCommonBlockCountWithCutoff m d j := by
  exact Finset.single_le_sum
    (f := fun r : Fin (d + 1) => preparedSamplerBlockCount m (r.val + 1) j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

theorem preparedCommonBlockCountWithCutoff_positive (m d : ℕ) (j : Fin m) :
    0 < preparedCommonBlockCountWithCutoff m d j :=
  (preparedSamplerBlockCount_positive m 1 j).trans_le (preparedCommonBlockCountWithCutoff_ge m d j 0)

theorem preparedCommonBlockCountWithCutoff_spectrum (m d : ℕ) (j : Fin m) (s : Fin (d + 1)) :
    let rows := boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedCommonBlockCountWithCutoff m d j :=
  (preparedSamplerBlockCount_spectrum m (s.val + 1) j).trans (preparedCommonBlockCountWithCutoff_ge m d j s)

theorem preparedCommonBlockCountWithCutoff_jets (m d : ℕ) (j : Fin m) (s : Fin (d + 1)) :
    Fintype.card (BoundedBooleanJet (Fin (s.val + 1)) (j.val + 1)) ≤ preparedCommonBlockCountWithCutoff m d j :=
  (preparedSamplerBlockCount_jets m (s.val + 1) j).trans (preparedCommonBlockCountWithCutoff_ge m d j s)

noncomputable def preparedCommonSamplerDimensionWithCutoff (m d M : ℕ) : ℕ :=
  (d + 1) * (d + 3) + M * m * (∑ j, preparedCommonBlockCountWithCutoff m d j) + M + m + 2

abbrev EnlargedPreparedCommonKernelWithCutoff (m d Jalloc : ℕ) :=
  Fin ((d + 1) * (d + 3) + (m + 1) * Jalloc)

theorem enlargedPreparedCommonKernelWithCutoff_analytic_capacity (m d Jalloc s : ℕ) (hs : s ≤ d) :
    (s + 1) * (s + 3) ≤ Fintype.card (EnlargedPreparedCommonKernelWithCutoff m d Jalloc) := by
  simp only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin]
  exact (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_add_right _ _)

theorem enlargedPreparedCommonKernelWithCutoff_allocation_capacity (m d Jalloc : ℕ) :
    Jalloc ≤ Fintype.card (EnlargedPreparedCommonKernelWithCutoff m d Jalloc) := by
  simp only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin]
  have h : Jalloc ≤ (m + 1) * Jalloc := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, one_mul] using
      Nat.mul_le_mul_right Jalloc (Nat.succ_le_succ (Nat.zero_le m))
  omega

theorem enlargedPreparedCommonKernelWithCutoff_multiple_capacity (m d Jalloc h : ℕ) (hh : h ≤ m) :
    h * Jalloc ≤ Fintype.card (EnlargedPreparedCommonKernelWithCutoff m d Jalloc) := by
  simp only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin]
  exact (Nat.mul_le_mul_right Jalloc (hh.trans (Nat.le_succ m))).trans (Nat.le_add_left _ _)

def enlargedPreparedCommonCanonicalSelectionWithCutoff (m d Jalloc s : ℕ) (hs : s ≤ d) :
    Fin (s + 1) ↪ EnlargedPreparedCommonKernelWithCutoff m d Jalloc where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt (by
    have hcap := enlargedPreparedCommonKernelWithCutoff_analytic_capacity m d Jalloc s hs
    have hsmall : s + 1 ≤ (s + 1) * (s + 3) := by nlinarith
    simpa only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin] using hsmall.trans hcap)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : EnlargedPreparedCommonKernelWithCutoff m d Jalloc => z.val) h)

@[simp] theorem enlargedPreparedCommonCanonicalSelectionWithCutoff_val (m d Jalloc s : ℕ)
    (hs : s ≤ d) (i : Fin (s + 1)) :
    (enlargedPreparedCommonCanonicalSelectionWithCutoff m d Jalloc s hs i).val = i.val := rfl

noncomputable def enlargedPreparedCommonSamplerDimensionWithCutoff (m d M Jalloc : ℕ) : ℕ :=
  (d + 1) * (d + 3) + (m + 1) * Jalloc +
    M * m * (∑ j : Fin m, (preparedCommonBlockCountWithCutoff m d j + Jalloc)) + M + m + Jalloc + 2

theorem enlargedPreparedCommonSamplerDimensionWithCutoff_polynomial (m d M Jalloc : ℕ) :
    enlargedPreparedCommonSamplerDimensionWithCutoff m d M Jalloc =
      preparedCommonSamplerDimensionWithCutoff m d M + (m + 2 + M * m * m) * Jalloc := by
  simp only [enlargedPreparedCommonSamplerDimensionWithCutoff, preparedCommonSamplerDimensionWithCutoff,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  ring

theorem enlargedPreparedCommonSamplerDimensionWithCutoff_ge (m d M Jalloc : ℕ) :
    M ≤ enlargedPreparedCommonSamplerDimensionWithCutoff m d M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimensionWithCutoff
  omega

theorem enlargedPreparedCommonSamplerDimensionWithCutoff_allocation (m d M Jalloc : ℕ) :
    Jalloc ≤ enlargedPreparedCommonSamplerDimensionWithCutoff m d M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimensionWithCutoff
  omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev EnlargedPreparedCommonSamplerBlockWithCutoff (d Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :=
  Fin (preparedCommonBlockCountWithCutoff m d a.1 + Jalloc)

theorem enlargedPreparedCommonSamplerBlockWithCutoff_allocation (d Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Jalloc ≤ Fintype.card (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc a) := by
  simp only [EnlargedPreparedCommonSamplerBlockWithCutoff, Fintype.card_fin]
  omega

theorem enlargedPreparedCommonSamplerBlockWithCutoff_positive (d Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    0 < Fintype.card (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlockWithCutoff, Fintype.card_fin] using
    (preparedCommonBlockCountWithCutoff_positive m d a.1).trans_le (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlockWithCutoff_jets (d Jalloc s : ℕ) (hs : s ≤ d)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Fintype.card (BoundedBooleanJet (Fin (s + 1)) (a.1.val + 1)) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlockWithCutoff, Fintype.card_fin] using
    (preparedCommonBlockCountWithCutoff_jets m d a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlockWithCutoff_spectrum (d Jalloc s : ℕ) (hs : s ≤ d)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    max (positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card)) ≤
        Fintype.card (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlockWithCutoff, Fintype.card_fin] using
    (preparedCommonBlockCountWithCutoff_spectrum m d a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlockWithCutoff_positiveModerate (d Jalloc s : ℕ) (hs : s ≤ d)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc a) := by
  dsimp only
  apply le_trans _ ((le_max_left _ _).trans
    (enlargedPreparedCommonSamplerBlockWithCutoff_spectrum L d Jalloc s hs a))
  unfold positiveModerateSpectrumBlockCount
  apply Nat.succ_le_succ
  apply max_le_max (le_refl _)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

theorem enlargedPreparedCommonSamplerBlockWithCutoff_uniform (d Jalloc s : ℕ) (hs : s ≤ d)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc a) :=
  (le_max_right _ _).trans (enlargedPreparedCommonSamplerBlockWithCutoff_spectrum L d Jalloc s hs a)

theorem enlargedPreparedCommonSamplerWithCutoff_variables_card (d Jalloc : ℕ) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernelWithCutoff m d Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc)) =
      (d + 1) * (d + 3) + (m + 1) * Jalloc + ∑ j : Fin m,
        Fintype.card (L j).Coord * ((preparedCommonBlockCountWithCutoff m d j + Jalloc) * (j.val + 1)) := by
  rw [samplerTupleIndex_card]
  simp only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin, LayerSamplerAxis, Fintype.sum_sigma,
    EnlargedPreparedCommonSamplerBlockWithCutoff, layerSamplerDegree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, Nat.cast_id] using
    congrArg (fun count : ℕ => count * ((preparedCommonBlockCountWithCutoff m d j + Jalloc) * (j.val + 1)))
      (preparedSampler_axis_card L j)

theorem enlargedPreparedCommonSamplerWithCutoff_dimensions (d Jalloc : ℕ) {M : ℕ}
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernelWithCutoff m d Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlockWithCutoff L d Jalloc)) ≤ enlargedPreparedCommonSamplerDimensionWithCutoff m d M Jalloc ∧
      (∀ j, Fintype.card (PreparedSamplerContinuous L j) ≤ enlargedPreparedCommonSamplerDimensionWithCutoff m d M Jalloc) ∧
      (∀ j, preparedSamplerTransverse L j ≤ enlargedPreparedCommonSamplerDimensionWithCutoff m d M Jalloc) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [enlargedPreparedCommonSamplerWithCutoff_variables_card]
    have hsum : (∑ j : Fin m, Fintype.card (L j).Coord *
        ((preparedCommonBlockCountWithCutoff m d j + Jalloc) * (j.val + 1))) ≤
        M * m * (∑ j : Fin m, (preparedCommonBlockCountWithCutoff m d j + Jalloc)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ M * ((preparedCommonBlockCountWithCutoff m d j + Jalloc) * m) :=
          Nat.mul_le_mul (hM j) (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt j.isLt))
        _ = _ := by ring
    unfold enlargedPreparedCommonSamplerDimensionWithCutoff
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimensionWithCutoff_ge m d M Jalloc
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimensionWithCutoff_ge m d M Jalloc
    omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

theorem preparedForecastJacobian_budget
    {m M nX : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    {R : Fin m → ℝ} {pRadius gainLog Pchart : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog) (hChart : 0 ≤ Pchart)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hcovol : ∀ j, ZLattice.covolume
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))) ≤ Real.exp Pchart)
    (L : ℕ) {gridVolume : ℝ} (hgrid : 1 ≤ gridVolume) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let Pκ := ((nX + m + m * M : ℕ) : ℝ) *
      (pRadius + gainLog + nX + Pchart + 11)
    0 < forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R L gridVolume τ ∧
    0 ≤ Pκ ∧
    forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R L gridVolume τ ≤ Real.exp Pκ := by
  intro τ Pκ
  let P := pRadius + gainLog + nX + Pchart + 8
  have hn : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; linarith
  have hrP : pRadius ≤ P := by dsimp only [P]; linarith
  have hcP : Pchart ≤ P := by dsimp only [P]; linarith
  have htP : gainLog + nX + 8 ≤ P := by dsimp only [P]; linarith
  have hτ : 0 < τ := Real.exp_pos _
  have hτinv : τ⁻¹ ≤ Real.exp P := by
    change (Real.exp (-(gainLog + (nX : ℝ) + 8)))⁻¹ ≤ Real.exp P
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr htP
  have hdim : Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
      Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤ m * M := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.sum_add_distrib]
    calc
      _ = ∑ j : Fin m, Fintype.card (prep j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [PreparedSamplerContinuous, Fintype.card_fin] using preparedSampler_axis_card prep j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hdimR := Nat.cast_le (α := ℝ).mpr hdim
  simp only [Nat.cast_add, Nat.cast_mul] at hdimR
  have hκ := forecastGeometricJacobian_uniform_le_exp
    (X := Fin nX) (I := PreparedSamplerContinuous prep) U b hR L hP hgrid hτ hτinv
    (fun j => (hRinv j).trans (Real.exp_le_exp.mpr hrP))
    (fun j => (hcovol j).trans (Real.exp_le_exp.mpr hcP))
  refine ⟨forecastGeometricJacobian_pos U b hR L (lt_of_lt_of_le zero_lt_one hgrid) hτ, ?_, ?_⟩
  · dsimp only [Pκ]
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  · apply hκ.trans (Real.exp_le_exp.mpr ?_)
    have hmult := mul_le_mul_of_nonneg_right
      (show (m : ℝ) + Fintype.card (Fin nX) +
        Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
        Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤
        ((nX + m + m * M : ℕ) : ℝ) by
          simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
          linarith) (show 0 ≤ P + 3 by linarith)
    apply hmult.trans_eq
    dsimp only [Pκ, P]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

abbrev EnlargedPreparedCommonKernel (m Jalloc : ℕ) :=
  Fin ((m + 1) * (m + 3) + (m + 1) * Jalloc)

theorem enlargedPreparedCommonKernel_analytic_capacity (m Jalloc s : ℕ) (hs : s ≤ m) :
    (s + 1) * (s + 3) ≤ Fintype.card (EnlargedPreparedCommonKernel m Jalloc) := by
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin]
  exact (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_add_right _ _)

theorem enlargedPreparedCommonKernel_allocation_capacity (m Jalloc : ℕ) :
    Jalloc ≤ Fintype.card (EnlargedPreparedCommonKernel m Jalloc) := by
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin]
  have h : Jalloc ≤ (m + 1) * Jalloc := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, one_mul] using
      Nat.mul_le_mul_right Jalloc (Nat.succ_le_succ (Nat.zero_le m))
  omega

theorem enlargedPreparedCommonKernel_multiple_capacity (m Jalloc h : ℕ) (hh : h ≤ m) :
    h * Jalloc ≤ Fintype.card (EnlargedPreparedCommonKernel m Jalloc) := by
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin]
  exact (Nat.mul_le_mul_right Jalloc (hh.trans (Nat.le_succ m))).trans (Nat.le_add_left _ _)

def enlargedPreparedCommonCanonicalSelection (m Jalloc s : ℕ) (hs : s ≤ m) :
    Fin (s + 1) ↪ EnlargedPreparedCommonKernel m Jalloc where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt (by
    have hcap := enlargedPreparedCommonKernel_analytic_capacity m Jalloc s hs
    have hsmall : s + 1 ≤ (s + 1) * (s + 3) := by nlinarith
    simpa only [EnlargedPreparedCommonKernel, Fintype.card_fin] using hsmall.trans hcap)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : EnlargedPreparedCommonKernel m Jalloc => z.val) h)

@[simp] theorem enlargedPreparedCommonCanonicalSelection_val (m Jalloc s : ℕ)
    (hs : s ≤ m) (i : Fin (s + 1)) :
    (enlargedPreparedCommonCanonicalSelection m Jalloc s hs i).val = i.val := rfl

noncomputable def enlargedPreparedCommonSamplerDimension (m M Jalloc : ℕ) : ℕ :=
  (m + 1) * (m + 3) + (m + 1) * Jalloc +
    M * m * (∑ j : Fin m, (preparedCommonBlockCount m j + Jalloc)) + M + m + Jalloc + 2

theorem enlargedPreparedCommonSamplerDimension_polynomial (m M Jalloc : ℕ) :
    enlargedPreparedCommonSamplerDimension m M Jalloc =
      preparedCommonSamplerDimension m M + (m + 2 + M * m * m) * Jalloc := by
  simp only [enlargedPreparedCommonSamplerDimension, preparedCommonSamplerDimension,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  ring

theorem enlargedPreparedCommonSamplerDimension_ge (m M Jalloc : ℕ) :
    M ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

theorem enlargedPreparedCommonSamplerDimension_allocation (m M Jalloc : ℕ) :
    Jalloc ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev EnlargedPreparedCommonSamplerBlock (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :=
  Fin (preparedCommonBlockCount m a.1 + Jalloc)

theorem enlargedPreparedCommonSamplerBlock_allocation (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Jalloc ≤ Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simp only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin]
  omega

theorem enlargedPreparedCommonSamplerBlock_positive (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    0 < Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_positive m a.1).trans_le (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_jets (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Fintype.card (BoundedBooleanJet (Fin (s + 1)) (a.1.val + 1)) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_jets m a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_spectrum (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    max (positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card)) ≤
        Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_spectrum m a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_positiveModerate (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  dsimp only
  apply le_trans _ ((le_max_left _ _).trans
    (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a))
  unfold positiveModerateSpectrumBlockCount
  apply Nat.succ_le_succ
  apply max_le_max (le_refl _)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

theorem enlargedPreparedCommonSamplerBlock_uniform (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) :=
  (le_max_right _ _).trans (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a)

theorem enlargedPreparedCommonSampler_variables_card (Jalloc : ℕ) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc)) =
      (m + 1) * (m + 3) + (m + 1) * Jalloc + ∑ j : Fin m,
        Fintype.card (L j).Coord * ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1)) := by
  rw [samplerTupleIndex_card]
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin, LayerSamplerAxis, Fintype.sum_sigma,
    EnlargedPreparedCommonSamplerBlock, layerSamplerDegree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, Nat.cast_id] using
    congrArg (fun d : ℕ => d * ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1)))
      (preparedSampler_axis_card L j)

theorem enlargedPreparedCommonSampler_dimensions (Jalloc : ℕ) {M : ℕ}
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc)) ≤ enlargedPreparedCommonSamplerDimension m M Jalloc ∧
      (∀ j, Fintype.card (PreparedSamplerContinuous L j) ≤ enlargedPreparedCommonSamplerDimension m M Jalloc) ∧
      (∀ j, preparedSamplerTransverse L j ≤ enlargedPreparedCommonSamplerDimension m M Jalloc) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [enlargedPreparedCommonSampler_variables_card]
    have hsum : (∑ j : Fin m, Fintype.card (L j).Coord *
        ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1))) ≤
        M * m * (∑ j : Fin m, (preparedCommonBlockCount m j + Jalloc)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ M * ((preparedCommonBlockCount m j + Jalloc) * m) :=
          Nat.mul_le_mul (hM j) (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt j.isLt))
        _ = _ := by ring
    unfold enlargedPreparedCommonSamplerDimension
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
    omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem forecast_block_card_le_variables
    {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (a : LayerSamplerAxis I n) :
    Fintype.card (B a) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  let f : B a → LayerSamplerVariables G I n B :=
    fun x => Sum.inr ⟨a, x, ⟨0, Nat.zero_lt_succ _⟩⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  simpa only [f, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, and_true, true_and] using h

theorem prepared_forecast_independent_scale_budget
    {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ)
    {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M)
    {Palloc Pearly pRadius : ℝ} (hPalloc : 0 ≤ Palloc) (hEarly : 0 ≤ Pearly)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ Palloc)
    (hRadius : pRadius ≤ Pearly) (R : Fin m → ℝ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) :
    0 ≤ Pearly + Palloc ∧
      (∀ j, (R j)⁻¹ ≤ Real.exp (Pearly + Palloc)) ∧
      (∀ j i, ((layerIntegerPrincipalSlots (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) j i).card : ℝ) ≤ Pearly + Palloc) := by
  apply forecastIndependentScaleBudget (EnlargedPreparedCommonSamplerBlock L Jalloc)
    hRadius hEarly hPalloc hRinv
  intro a
  exact (Nat.cast_le.mpr (forecast_block_card_le_variables
    (G := EnlargedPreparedCommonKernel m Jalloc) (EnlargedPreparedCommonSamplerBlock L Jalloc) a)).trans
    ((Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions L Jalloc hM).1).trans hnum)

end Erdos3.VectorPolynomial

end

end OAI
