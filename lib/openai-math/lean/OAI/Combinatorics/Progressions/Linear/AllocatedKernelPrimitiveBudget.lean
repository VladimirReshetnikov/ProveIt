import OAI.Combinatorics.Progressions.Estimates.DiscreteMinorThreshold
import OAI.Combinatorics.Progressions.Estimates.FiniteEventUnion
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeCokernelCutoff
import OAI.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
import OAI.Combinatorics.Progressions.Linear.KernelBudgetEnvelope
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI


namespace Erdos3

def GoodScalarKernelTuple {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {L : ℕ} (s : I → J) (κ : ℝ) (B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  κ < |normalizedScalarCubeMinor s x| ∧
    HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B

theorem scalarKernel_bad_event_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (p : FiniteProbabilityWeights (J → IntegerScalarCubeBox I L))
    (s : I → J) (κ : ℝ) (B : ℕ) (hκ : 0 < κ) :
    p.eventProbability (fun x => ¬ GoodScalarKernelTuple s κ B x) ≤
      p.eventProbability (fun x => |normalizedScalarCubeMinor s x| ≤ κ) +
        p.eventProbability (scalarCubeLargeCokernelEvent B) := by
  apply (p.eventProbability_mono _
    (fun x => |normalizedScalarCubeMinor s x| ≤ κ ∨ scalarCubeLargeCokernelEvent B x) ?_).trans
    (p.eventProbability_or_le _ _)
  intro x hx
  by_cases hsmall : |normalizedScalarCubeMinor s x| ≤ κ
  · exact Or.inl hsmall
  · apply Or.inr
    have hminor : ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0 := by
      intro hz
      apply hsmall
      simpa only [normalizedScalarCubeMinor, hz, Int.cast_zero, zero_div, abs_zero] using hκ.le
    have hp : ¬ HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B :=
      fun hp => hx ⟨lt_of_not_ge hsmall, hp⟩
    exact (scalarCube_no_bounded_period_iff B x).mp ⟨⟨s, hminor⟩, hp⟩

theorem exists_uniform_good_scalar_kernel_tuples (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    ∃ s : I ↪ J, ∀ η : ℝ, 0 < η → ∃ (κ : ℝ) (B L₀ : ℕ),
      0 < κ ∧ 0 < B ∧ Fintype.card I + 1 ≤ L₀ ∧ ∀ (L : ℕ) (hL : 0 < L), L₀ ≤ L →
        (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
          (fun x => ¬ GoodScalarKernelTuple s κ B x) ≤ η := by
  classical
  have hcard : Fintype.card I ≤ Fintype.card J := by rw [hJ]; nlinarith
  obtain ⟨s⟩ := Function.Embedding.nonempty_of_card_le hcard
  let : Nonempty J := ⟨s (Classical.choice (inferInstance : Nonempty I))⟩
  let N := Fintype.card (J × Option I)
  let e : J × Option I ≃ Fin N := Fintype.equivFin _
  have hN : 0 < N := Fintype.card_pos
  refine ⟨s, fun η hη => ?_⟩
  let κ := discreteScalarMinorThreshold I J N η
  have hκ : 0 < κ := discreteScalarMinorThreshold_pos I J hN hη
  obtain ⟨L₀, hsize, hreal⟩ := exists_discrete_minor_length I J e hN s s.injective η hη
  obtain ⟨B, hB, hperiod⟩ := exists_scalarCube_cokernel_cutoff I J hJ (η / 2) (half_pos hη)
  refine ⟨κ, B, L₀, hκ, hB, hsize, fun L hL hlarge => ?_⟩
  apply (scalarKernel_bad_event_le _ s κ B hκ).trans
  have hr := hreal L hL hlarge
  have hp : (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (scalarCubeLargeCokernelEvent B) ≤ η / 2 := by
    have hevents : stridedScalarCubeLargeCokernelEvent (I := I) (J := J) (L := L) 1 (1 * B) =
        scalarCubeLargeCokernelEvent B := by
      funext x
      simp only [stridedScalarCubeLargeCokernelEvent, scalarCubeLargeCokernelEvent,
        Nat.cast_one, one_smul, one_mul]
    have hp := hperiod L 1 hL (hsize.trans hlarge) Nat.zero_lt_one
    rwa [hevents] at hp
  exact (add_le_add hr hp).trans_eq (by ring)


noncomputable def scalarKernelConditioningConstant (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) : ℝ := (scalarCubeResidueDensityCap I (M * D)) ^ Fintype.card J

noncomputable def scalarKernelTailConstant (I J : Type*) [Fintype I] [Fintype J] : ℝ :=
  (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^ Fintype.card J

noncomputable def scalarKernelAdjustedAccuracy (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℝ := η / scalarKernelConditioningConstant I J M D

noncomputable def scalarKernelThreshold (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℝ :=
  discreteScalarMinorThreshold I J (Fintype.card (J × Option I))
    (scalarKernelAdjustedAccuracy I J M D η)

noncomputable def scalarKernelCutoff (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℕ :=
  jointKernelCutoff (Fintype.card I + 1) (D * ((Fintype.card I + 1) * M))
    (coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))))
    (scalarKernelTailConstant I J) (scalarKernelAdjustedAccuracy I J M D η)
    (scalarKernelThreshold I J M D η)

theorem scalarKernelConditioningConstant_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D) : 0 < scalarKernelConditioningConstant I J M D :=
  pow_pos (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)) _

theorem scalarKernelTailConstant_pos (I J : Type*) [Fintype I] [Fintype J] :
    0 < scalarKernelTailConstant I J := by
  unfold scalarKernelTailConstant
  exact pow_pos (mul_pos (integerScalarCubeDensityCap_pos I) (by positivity)) _

theorem scalarKernelAdjustedAccuracy_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelAdjustedAccuracy I J M D η :=
  div_pos hη (scalarKernelConditioningConstant_pos I J hM hD)

theorem scalarKernelThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelThreshold I J M D η := by
  unfold scalarKernelThreshold discreteScalarMinorThreshold
  apply polynomialSublevelThreshold_pos
  · apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  · positivity
  · exact scalarKernelAdjustedAccuracy_pos I J hM hD hη

theorem scalarKernelCutoff_bounds (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelCutoff I J M D η ∧
    Fintype.card I + 1 ≤ scalarKernelCutoff I J M D η ∧
    D * ((Fintype.card I + 1) * M) ≤ scalarKernelCutoff I J M D η ∧
    1 / scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) /
        scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    2 * scalarKernelTailConstant I J / scalarKernelAdjustedAccuracy I J M D η ≤
      (scalarKernelCutoff I J M D η : ℝ) :=
  jointKernelCutoff_bounds _ _ (coordinateDeterminantVariation_nonneg _ _)
    (scalarKernelTailConstant_pos I J).le (scalarKernelAdjustedAccuracy_pos I J hM hD hη)
    (scalarKernelThreshold_pos I J hM hD hη)


noncomputable def normalizedScalarCubePivot {I J : Type*} {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) : Matrix I I ℝ :=
  fun i j => (x (s j) (some i) : ℤ) / (L : ℝ)

theorem normalizedScalarCubePivot_det {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    (normalizedScalarCubePivot s x).det = normalizedScalarCubeMinor s x := by
  let e := Fintype.equivFin (J × Option I)
  have h := scalarCubeMinorPolynomial_grid_eval e s x
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval] at h
  change Matrix.det (fun i j => ((x (s j) (some i) : ℤ) : ℝ) / (L : ℝ)) = _
  simpa only [scalarCubeGrid, e.symm_apply_apply] using h

theorem normalizedScalarCubePivot_entry_bound {I J : Type*} {L : ℕ}
    (hL : 0 < L) (s : I → J) (x : J → IntegerScalarCubeBox I L) (i j : I) :
    |normalizedScalarCubePivot s x i j| ≤ 1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hx := Finset.mem_Ico.mp (x (s j) (some i)).property
  change |((x (s j) (some i) : ℤ) : ℝ) / (L : ℝ)| ≤ 1
  rw [abs_div, abs_of_pos hL']
  apply (div_le_one hL').mpr
  exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩

theorem goodScalarKernelTuple_pivot_inverse {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (hL : 0 < L) (s : I → J) (κ : ℝ) (B : ℕ) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple s κ B x) :
    (matrixSupCLM (normalizedScalarCubePivot s x)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedScalarCubePivot s x)).inverse‖ ≤
        Fintype.card I * ((Fintype.card I).factorial : ℝ) / κ := by
  have hd : κ ≤ |(normalizedScalarCubePivot s x).det| := by
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have h := matrixSupCLM_inverse_norm_le (normalizedScalarCubePivot s x) zero_le_one
    (normalizedScalarCubePivot_entry_bound hL s x) hκ hd
  simpa only [one_pow, mul_one, mul_div_assoc] using h


theorem hasBoundedScalarPeriod_mono {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) {B B' : ℕ} (hB : B ≤ B')
    (h : HasBoundedScalarPeriod L B) : HasBoundedScalarPeriod L B' := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  exact ⟨a, ha, haB.trans hB, hperiod⟩

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

theorem goodScalarKernelTuple_mono {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L : ℕ}
    (s : I → J) {κ κ' : ℝ} {B B' : ℕ} (hκ : κ' ≤ κ) (hB : B ≤ B')
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple s κ B x) :
    GoodScalarKernelTuple s κ' B' x :=
  ⟨hκ.trans_lt hx.1, hasBoundedScalarPeriod_mono _ hB hx.2⟩

theorem exists_uniform_good_scalar_kernel_bound (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    ∃ s : I ↪ J, ∀ η : ℝ, 0 < η → ∃ B L₀ : ℕ,
      0 < B ∧ Fintype.card I + 1 ≤ L₀ ∧ ∀ (L : ℕ) (hL : 0 < L), L₀ ≤ L →
        (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
          (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) ≤ η := by
  obtain ⟨s, hs⟩ := exists_uniform_good_scalar_kernel_tuples I J hJ
  refine ⟨s, fun η hη => ?_⟩
  obtain ⟨κ, B, L₀, hκ, hB, hL₀, hprob⟩ := hs η hη
  obtain ⟨C, hC⟩ := exists_nat_gt (max 1 (1 / κ))
  let B' := max B C
  have hBB' : B ≤ B' := Nat.le_max_left _ _
  have hB' : 0 < B' := hB.trans_le hBB'
  have hbound : 1 / κ ≤ (B' : ℝ) :=
    ((le_max_right _ _).trans hC.le).trans (by exact_mod_cast Nat.le_max_right B C)
  have hsmall : 1 / (B' : ℝ) ≤ κ := by
    apply (div_le_iff₀ (by exact_mod_cast hB')).mpr
    have h := (div_le_iff₀ hκ).mp hbound
    nlinarith
  refine ⟨B', L₀, hB', hL₀, fun L hL hlarge => ?_⟩
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans (hprob L hL hlarge)
  intro x hx hold
  exact hx (goodScalarKernelTuple_mono s hsmall hBB' x hold)


noncomputable def scalarKernelCutoffLogBudget (I J : Type*) [Fintype I] [Fintype J] (P : ℝ) : ℝ :=
  2 * ((4 + 3 * ((Fintype.card (J × Option I) * Fintype.card I : ℕ) : ℝ)) * (P + 2)) + 8

theorem scalarKernelCutoff_le_exp_of_bounds (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η P : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hP : 1 ≤ P)
    (hnP : (Fintype.card I + 1 : ℝ) ≤ Real.exp P)
    (hbP : (D * ((Fintype.card I + 1) * M) : ℕ) ≤ Real.exp P)
    (hKP : coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) ≤ Real.exp P)
    (hTP : scalarKernelTailConstant I J ≤ Real.exp P)
    (hεP : (scalarKernelAdjustedAccuracy I J M D η)⁻¹ ≤ Real.exp P)
    (hCP : (integerScalarCubeDensityCap I) ^ Fintype.card J *
      multivariateSublevelConstant (Fintype.card (J × Option I)) (Fintype.card I) ≤ Real.exp P)
    (hSP : (Fintype.card I + 1 : ℝ) ^ Fintype.card (J × Option I) ≤ Real.exp P) :
    (scalarKernelCutoff I J M D η : ℝ) ≤ Real.exp (scalarKernelCutoffLogBudget I J P) := by
  let a : ℝ := ((Fintype.card (J × Option I) * Fintype.card I : ℕ) : ℝ)
  let Q := (4 + 3 * a) * (P + 2)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPQ : P ≤ Q := by dsimp [Q]; nlinarith
  have hQ : 0 ≤ Q := hP0.trans hPQ
  have hκ := scalarKernelThreshold_pos I J hM hD hη
  have hε := scalarKernelAdjustedAccuracy_pos I J hM hD hη
  have hC : 0 ≤ (integerScalarCubeDensityCap I) ^ Fintype.card J *
      multivariateSublevelConstant (Fintype.card (J × Option I)) (Fintype.card I) := by
    apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  have hS : 0 ≤ (Fintype.card I + 1 : ℝ) ^ Fintype.card (J × Option I) := by positivity
  have h2 : (1 + 1 : ℝ) ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have ht := polynomialSublevelThreshold_log_budget
    (Fintype.card (J × Option I) * Fintype.card I) 1 hC hS hε hP0 hCP hSP
    (by simpa only [Nat.cast_one] using h2) hεP
  have hlog : Real.log (scalarKernelThreshold I J M D η)⁻¹ ≤
      (1 + 3 * a) * P + 2 * Real.log 2 + a * Real.log 3 := ht
  have hlog2 : Real.log 2 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog3 : Real.log 3 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hκQ : (scalarKernelThreshold I J M D η)⁻¹ ≤ Real.exp Q := by
    apply (Real.log_le_iff_le_exp (inv_pos.mpr hκ)).mp
    apply hlog.trans
    have h3 := mul_le_mul_of_nonneg_left hlog3 ha
    dsimp [Q]
    nlinarith
  have hexp : Real.exp P ≤ Real.exp Q := Real.exp_le_exp.mpr hPQ
  exact jointKernelCutoff_le_exp _ _ (coordinateDeterminantVariation_nonneg _ _)
    (scalarKernelTailConstant_pos I J).le hε hκ hQ
    (by simpa only [Nat.cast_add, Nat.cast_one] using hnP.trans hexp)
    (hbP.trans hexp) (hKP.trans hexp) (hTP.trans hexp) (hεP.trans hexp) hκQ


theorem univariateSublevelConstant_le_exp (q : ℕ) (hq : 0 < q) :
    univariateSublevelConstant q ≤ Real.exp ((q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
  have hn : (q + 1 : ℝ) ≤ Real.exp (q + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (q + 1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hbase : 1 ≤ (q + 1 : ℝ) * (8 * (q + 1 : ℝ)) ^ q := by
    have hp : 1 ≤ (8 * (q + 1 : ℝ)) ^ q := one_le_pow₀ (by have := Nat.cast_nonneg q (α := ℝ); linarith)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hi : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hm : 8 * (q + 1 : ℝ) ≤ Real.exp (8 + (q + 1 : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul h8 hn (by positivity) (Real.exp_pos _).le
  calc
    _ ≤ (q + 1 : ℝ) * (8 * (q + 1 : ℝ)) ^ q := by
      simpa only [univariateSublevelConstant, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hbase hi
    _ ≤ Real.exp (q + 1 : ℝ) * Real.exp (8 + (q + 1 : ℝ)) ^ q := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem multivariateSublevelConstant_le_exp (N q : ℕ) (hq : 0 < q) :
    multivariateSublevelConstant N q ≤
      Real.exp (3 * (N : ℝ) + (q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hN : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hu0 := (univariateSublevelConstant_pos q).le
  have hu := univariateSublevelConstant_le_exp q hq
  unfold multivariateSublevelConstant
  calc
    _ ≤ (Real.exp 2) ^ N * Real.exp N *
        Real.exp ((q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem integerScalarCubeDensityCap_le_exp (I : Type*) [Fintype I] :
    integerScalarCubeDensityCap I ≤
      Real.exp ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  unfold integerScalarCubeDensityCap
  push_cast
  calc
    _ ≤ (Real.exp 4 * Real.exp (Fintype.card I + 1 : ℝ)) ^ (Fintype.card I + 1) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; push_cast; rfl

theorem scalarKernelTailConstant_le_exp (I J : Type*) [Fintype I] [Fintype J] :
    scalarKernelTailConstant I J ≤ Real.exp ((Fintype.card J : ℝ) *
      ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ)) + (Fintype.card I : ℝ)^2 + 1)) := by
  have hf := factorial_le_exp_sq (Fintype.card I)
  have hA0 := (integerScalarCubeDensityCap_pos I).le
  have hA := integerScalarCubeDensityCap_le_exp I
  have hE : 1 ≤ Real.exp ((Fintype.card I : ℝ)^2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hs : 1 + ((Fintype.card I).factorial : ℝ) ≤ Real.exp ((Fintype.card I : ℝ)^2 + 1) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos ((Fintype.card I : ℝ)^2)).le]
  unfold scalarKernelTailConstant
  calc
    _ ≤ (Real.exp ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) *
        Real.exp ((Fintype.card I : ℝ)^2 + 1)) ^ Fintype.card J := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring

theorem coordinateDeterminantVariation_le_exp (I : Type*) [Fintype I] (N : ℕ) :
    coordinateDeterminantVariation I (Fin N) ≤
      Real.exp ((N : ℝ) + (Fintype.card I : ℝ)^2 + Fintype.card I) := by
  have hN : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hq : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  simp only [coordinateDeterminantVariation, Fintype.card_fin]
  calc
    _ ≤ Real.exp N * (Real.exp ((Fintype.card I : ℝ)^2) * Real.exp (Fintype.card I : ℝ)) := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


theorem scalarKernel_explicit_probability_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) (s : I ↪ J)
    {M D L : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hL : 0 < L)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
        (scalarKernelCutoff I J M D η) x) ≤ scalarKernelAdjustedAccuracy I J M D η := by
  let B := scalarKernelCutoff I J M D η
  let κ := scalarKernelThreshold I J M D η
  let ε := scalarKernelAdjustedAccuracy I J M D η
  obtain ⟨hB, hsize, _, hinv, hmesh, htail⟩ := scalarKernelCutoff_bounds I J hM hD hη
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hκ : 0 < κ := scalarKernelThreshold_pos I J hM hD hη
  have hε : 0 < ε := scalarKernelAdjustedAccuracy_pos I J hM hD hη
  have hsizeL : Fintype.card I + 1 ≤ L := hsize.trans hlarge
  have hsmall : 1 / (B : ℝ) ≤ κ := by
    apply (div_le_iff₀ hB').mpr
    have h := (div_le_iff₀ hκ).mp hinv
    nlinarith
  have hmeshL : coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) / L ≤ κ := by
    apply (div_le_iff₀ hL').mpr
    have hBL : (scalarKernelCutoff I J M D η : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlarge
    have h := (div_le_iff₀ hκ).mp (hmesh.trans hBL)
    nlinarith
  have htailB : scalarKernelTailConstant I J / B ≤ ε / 2 := by
    apply (div_le_iff₀ hB').mpr
    have h := (div_le_iff₀ hε).mp htail
    nlinarith
  have hJpos : 0 < Fintype.card J := by
    rw [hJ]
    exact Nat.mul_pos Fintype.card_pos (by omega)
  have hN : 0 < Fintype.card (J × Option I) := by
    rw [Fintype.card_prod, Fintype.card_option]
    exact Nat.mul_pos hJpos (by omega)
  have hreal := discrete_minor_threshold_probability (Fintype.equivFin (J × Option I)) hN
    s s.injective L hL hsizeL ε hε hmeshL
  have hminor : (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ 1 / (B : ℝ)) ≤ ε / 2 := by
    apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans hreal
    intro x hx
    exact hx.trans hsmall
  have hcoker := scalarCube_largeCokernel_probability_le (I := I) (J := J) L B hL hsizeL hB hJ
  apply (scalarKernel_bad_event_le _ s (1 / (B : ℝ)) B (one_div_pos.mpr hB')).trans
  exact (add_le_add hminor (hcoker.trans htailB)).trans_eq (by ring)


theorem scalarKernelConditioningConstant_le_exp (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) {R : ℝ} (hM : (M : ℝ) ≤ Real.exp R) (hD : (D : ℝ) ≤ Real.exp R) :
    scalarKernelConditioningConstant I J M D ≤ Real.exp ((Fintype.card J : ℝ) *
      (Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ) + 2 * R)) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hbase : 4 * (Fintype.card I + 1 : ℝ) * ((M : ℝ) * D) ≤
      Real.exp (4 + (Fintype.card I + 1 : ℝ) + 2 * R) := by
    calc
      _ ≤ Real.exp 4 * Real.exp (Fintype.card I + 1 : ℝ) * (Real.exp R * Real.exp R) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  unfold scalarKernelConditioningConstant scalarCubeResidueDensityCap
  push_cast
  calc
    _ ≤ (Real.exp (4 + (Fintype.card I + 1 : ℝ) + 2 * R) ^ (Fintype.card I + 1)) ^ Fintype.card J := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem scalarKernelAdjustedAccuracy_inv_le_exp (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) {R η : ℝ} (hη : 0 < η) (hM : (M : ℝ) ≤ Real.exp R)
    (hD : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    (scalarKernelAdjustedAccuracy I J M D η)⁻¹ ≤ Real.exp ((Fintype.card J : ℝ) *
      (Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ) + 2 * R) + R) := by
  rw [scalarKernelAdjustedAccuracy, inv_div, div_eq_mul_inv, Real.exp_add]
  exact mul_le_mul (scalarKernelConditioningConstant_le_exp I J M D hM hD) hηR
    (inv_nonneg.mpr hη.le) (Real.exp_pos _).le

theorem scalarKernelMinorConstant_le_exp (I J : Type*) [Fintype I] [Nonempty I] [Fintype J] (N : ℕ) :
    (integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I) ≤
      Real.exp ((Fintype.card J : ℝ) * ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) +
        3 * (N : ℝ) + (Fintype.card I + 1 : ℝ) + Fintype.card I * (8 + (Fintype.card I + 1 : ℝ))) := by
  have hA := integerScalarCubeDensityCap_le_exp I
  have hA0 := (integerScalarCubeDensityCap_pos I).le
  have hC := multivariateSublevelConstant_le_exp N (Fintype.card I) Fintype.card_pos
  have hC0 : 0 ≤ multivariateSublevelConstant N (Fintype.card I) := by
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  calc
    _ ≤ Real.exp ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) ^ Fintype.card J *
        Real.exp (3 * (N : ℝ) + (Fintype.card I + 1 : ℝ) + Fintype.card I * (8 + (Fintype.card I + 1 : ℝ))) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem scalarKernelMinorScale_le_exp (I : Type*) [Fintype I] (N : ℕ) :
    (Fintype.card I + 1 : ℝ) ^ N ≤ Real.exp ((N : ℝ) * (Fintype.card I + 1 : ℝ)) := by
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  calc
    _ ≤ Real.exp (Fintype.card I + 1 : ℝ) ^ N := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm


noncomputable def scalarKernelInputBudget (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : ℝ :=
  16 * (10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card (J × Option I) + R)^3

theorem scalarKernelInputBudget_bounds (I J : Type*)
    [Fintype I] [Nonempty I] [Fintype J] (M D : ℕ) {R η : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hM : (M : ℝ) ≤ Real.exp R)
    (hD : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    1 ≤ scalarKernelInputBudget I J R ∧
    (Fintype.card I + 1 : ℝ) ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    (D * ((Fintype.card I + 1) * M) : ℕ) ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    scalarKernelTailConstant I J ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    (scalarKernelAdjustedAccuracy I J M D η)⁻¹ ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    (integerScalarCubeDensityCap I)^Fintype.card J *
      multivariateSublevelConstant (Fintype.card (J × Option I)) (Fintype.card I) ≤
        Real.exp (scalarKernelInputBudget I J R) ∧
    (Fintype.card I + 1 : ℝ)^Fintype.card (J × Option I) ≤ Real.exp (scalarKernelInputBudget I J R) := by
  let Q : ℝ := 10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card (J × Option I) + R
  have hq0 : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ Fintype.card (J × Option I) := Nat.cast_nonneg _
  obtain ⟨hP, hn, hb, hK, hT, hε, hC, hS⟩ := scalarKernel_polynomial_envelope (Q := Q)
    hq0 hj0 hN0 hR (by dsimp [Q]; linarith) (by dsimp [Q]; linarith)
    (by dsimp [Q]; linarith) (by dsimp [Q]; linarith) (by dsimp [Q]; linarith)
  have hPE : 16 * Q^3 ≤ Real.exp (16 * Q^3) := by linarith [Real.add_one_le_exp (16 * Q^3)]
  have hnE : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hbE : ((D * ((Fintype.card I + 1) * M) : ℕ) : ℝ) ≤
      Real.exp (2 * R + (Fintype.card I + 1 : ℝ)) := by
    push_cast
    calc
      _ ≤ Real.exp R * (Real.exp (Fintype.card I + 1 : ℝ) * Real.exp R) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨hP, hn.trans hPE, hbE.trans (Real.exp_le_exp.mpr hb), ?_, ?_, ?_, ?_, ?_⟩
  · exact (coordinateDeterminantVariation_le_exp I _).trans (Real.exp_le_exp.mpr hK)
  · exact (scalarKernelTailConstant_le_exp I J).trans (Real.exp_le_exp.mpr hT)
  · exact (scalarKernelAdjustedAccuracy_inv_le_exp I J M D hη hM hD hηR).trans (Real.exp_le_exp.mpr hε)
  · exact (scalarKernelMinorConstant_le_exp I J _).trans (Real.exp_le_exp.mpr hC)
  · exact (scalarKernelMinorScale_le_exp I _).trans (Real.exp_le_exp.mpr hS)


noncomputable def scalarKernelLogarithmicBudget (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : ℝ :=
  scalarKernelCutoffLogBudget I J (scalarKernelInputBudget I J R)

theorem scalarKernelCutoff_le_exp (I J : Type*) [Fintype I] [Nonempty I] [Fintype J]
    {M D : ℕ} {R η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hR : 0 ≤ R)
    (hMR : (M : ℝ) ≤ Real.exp R) (hDR : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    (scalarKernelCutoff I J M D η : ℝ) ≤ Real.exp (scalarKernelLogarithmicBudget I J R) := by
  obtain ⟨hP, hn, hb, hK, hT, hε, hC, hS⟩ := scalarKernelInputBudget_bounds I J M D hR hη hMR hDR hηR
  exact scalarKernelCutoff_le_exp_of_bounds I J hM hD hη hP hn hb hK hT hε hC hS

theorem scalarKernelLogarithmicBudget_eq (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) :
    scalarKernelLogarithmicBudget I J R =
      2 * ((4 + 3 * ((Fintype.card J : ℝ) * (Fintype.card I + 1) * Fintype.card I)) *
        (16 * (10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card J * (Fintype.card I + 1) + R)^3 + 2)) + 8 := by
  simp only [scalarKernelLogarithmicBudget, scalarKernelCutoffLogBudget, scalarKernelInputBudget,
    Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

end Erdos3


namespace Erdos3.VectorPolynomial

noncomputable def allocatedKernelPrimitiveBudget {A : Type*} [Semiring A]
    (p E T : A) : A :=
  let r := p + E + T + 1
  r + 2 * ((4 + 3 * (r * (r + 1) * r)) *
    (16 * (10 + r + r + r * (r + 1) + r)^3 + 2)) + 8

theorem allocatedKernelPrimitiveBudget_bounds {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    let Q := allocatedKernelPrimitiveBudget p E T
    0 ≤ Q ∧ p ≤ Q ∧ E ≤ Q ∧ T ≤ Q ∧ p + E + T + 1 ≤ Q := by
  have hr : 0 ≤ p + E + T + 1 := by positivity
  have hrest : 0 ≤ 2 * ((4 + 3 * ((p + E + T + 1) * (p + E + T + 1 + 1) *
      (p + E + T + 1))) * (16 * (10 + (p + E + T + 1) + (p + E + T + 1) +
      (p + E + T + 1) * (p + E + T + 1 + 1) + (p + E + T + 1))^3 + 2)) := by positivity
  dsimp only [allocatedKernelPrimitiveBudget]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedKernelPrimitiveBudget_mono {p E T p' E' T' : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hpp : p ≤ p') (hEE : E ≤ E') (hTT : T ≤ T') :
    allocatedKernelPrimitiveBudget p E T ≤ allocatedKernelPrimitiveBudget p' E' T' := by
  have hr : 0 ≤ p + E + T + 1 := by positivity
  have hrr : p + E + T + 1 ≤ p' + E' + T' + 1 := by linarith
  have hr' : 0 ≤ p' + E' + T' + 1 := hr.trans hrr
  dsimp only [allocatedKernelPrimitiveBudget]
  gcongr

theorem scalarKernelLogarithmicBudget_le_allocatedPrimitive
    (I G : Type*) [Fintype I] [Fintype G] {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hI : (Fintype.card I : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p) :
    scalarKernelLogarithmicBudget I G (p + E + T + 1) ≤ allocatedKernelPrimitiveBudget p E T := by
  let r := p + E + T + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hIr : (Fintype.card I : ℝ) ≤ r := by dsimp [r]; linarith
  have hGr : (Fintype.card G : ℝ) ≤ r := by dsimp [r]; linarith
  rw [scalarKernelLogarithmicBudget_eq]
  change 2 * ((4 + 3 * ((Fintype.card G : ℝ) * (Fintype.card I + 1) * Fintype.card I)) *
    (16 * (10 + (Fintype.card I : ℝ) + Fintype.card G + Fintype.card G * (Fintype.card I + 1) + r)^3 + 2)) + 8 ≤ _
  have hcore : 2 * ((4 + 3 * ((Fintype.card G : ℝ) * (Fintype.card I + 1) * Fintype.card I)) *
      (16 * (10 + (Fintype.card I : ℝ) + Fintype.card G + Fintype.card G * (Fintype.card I + 1) + r)^3 + 2)) ≤
      2 * ((4 + 3 * (r * (r + 1) * r)) * (16 * (10 + r + r + r * (r + 1) + r)^3 + 2)) := by
    gcongr
  dsimp only [allocatedKernelPrimitiveBudget]
  change _ ≤ r + 2 * ((4 + 3 * (r * (r + 1) * r)) *
    (16 * (10 + r + r + r * (r + 1) + r)^3 + 2)) + 8
  linarith

theorem exists_allocatedKernelThreshold_bound (A : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E T : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ T →
      (allocatedKernelPrimitiveBudget p E T + (E + 1) + (T + 1) + A)^A ≤
        (p + E + T + a)^a := by
  let poly : Polynomial ℕ :=
    (allocatedKernelPrimitiveBudget Polynomial.X Polynomial.X Polynomial.X +
      (Polynomial.X + 1) + (Polynomial.X + 1) + (A : Polynomial ℕ))^A
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p E T hp hE hT
  have hpq : p ≤ p + E + T := by linarith
  have hEq : E ≤ p + E + T := by linarith
  have hTq : T ≤ p + E + T := by linarith
  have hQ := allocatedKernelPrimitiveBudget_mono hp hE hT hpq hEq hTq
  have hbase : allocatedKernelPrimitiveBudget p E T + (E + 1) + (T + 1) + A ≤
      allocatedKernelPrimitiveBudget (p + E + T) (p + E + T) (p + E + T) +
        (p + E + T + 1) + (p + E + T + 1) + A := by linarith
  have hnonneg := (allocatedKernelPrimitiveBudget_bounds hp hE hT).1
  apply (pow_le_pow_left₀ (by positivity) hbase A).trans
  simpa [poly, allocatedKernelPrimitiveBudget, Polynomial.eval₂_pow] using
    hbound (p + E + T) (by positivity)

end Erdos3.VectorPolynomial

end OAI
