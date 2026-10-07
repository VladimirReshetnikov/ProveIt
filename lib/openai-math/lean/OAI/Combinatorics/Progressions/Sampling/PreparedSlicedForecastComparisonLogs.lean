import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedSourceLog
import OAI.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastPrimitiveCap : ℝ :=
  max 1 (scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound 1 0 1)

noncomputable def preparedSlicedForecastTailCap (cost : ℝ) : ℝ :=
  max preparedSlicedForecastPrimitiveCap (2 * Real.exp cost)

noncomputable def preparedSlicedForecastTailLog (cost : ℝ) : ℝ :=
  preparedSlicedForecastPrimitiveCap + cost + 1

noncomputable def preparedSlicedForecastDensity (cost : ℝ) : ℝ :=
  Real.exp (-cost)

def preparedSlicedForecastKernelLog (cost : ℝ) : ℝ := cost + 1

noncomputable def preparedSlicedForecastChildSize (childLog : ℝ) : ℕ :=
  ⌈Real.exp childLog⌉₊

theorem preparedSlicedForecastPrimitiveCap_one_le :
    1 ≤ preparedSlicedForecastPrimitiveCap := le_max_left _ _

theorem preparedSlicedForecastTailCap_primitive_le (cost : ℝ) :
    preparedSlicedForecastPrimitiveCap ≤ preparedSlicedForecastTailCap cost :=
  le_max_left _ _

theorem preparedSlicedForecastTailCap_stride_le (cost : ℝ) :
    2 * Real.exp cost ≤ preparedSlicedForecastTailCap cost := le_max_right _ _

theorem preparedSlicedForecastTailCap_one_le (cost : ℝ) :
    1 ≤ preparedSlicedForecastTailCap cost :=
  preparedSlicedForecastPrimitiveCap_one_le.trans
    (preparedSlicedForecastTailCap_primitive_le cost)

theorem preparedSlicedForecastTailLog_nonneg {cost : ℝ} (hcost : 0 ≤ cost) :
    0 ≤ preparedSlicedForecastTailLog cost := by
  unfold preparedSlicedForecastTailLog
  linarith only [hcost, preparedSlicedForecastPrimitiveCap_one_le]

theorem preparedSlicedForecastKernelLog_nonneg {cost : ℝ} (hcost : 0 ≤ cost) :
    0 ≤ preparedSlicedForecastKernelLog cost := by
  unfold preparedSlicedForecastKernelLog
  linarith

theorem preparedSlicedForecastDensity_pos (cost : ℝ) :
    0 < preparedSlicedForecastDensity cost := Real.exp_pos _

theorem preparedSlicedForecastDensity_inv (cost : ℝ) :
    (preparedSlicedForecastDensity cost)⁻¹ = Real.exp cost := by
  simp only [preparedSlicedForecastDensity, ← Real.exp_neg, neg_neg]

theorem preparedSlicedForecastTailCap_le_exp {cost : ℝ} (hcost : 0 ≤ cost) :
    preparedSlicedForecastTailCap cost ≤ Real.exp (preparedSlicedForecastTailLog cost) := by
  have hC := preparedSlicedForecastPrimitiveCap_one_le
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    norm_num at this ⊢
    exact this
  unfold preparedSlicedForecastTailCap preparedSlicedForecastTailLog
  refine max_le ?_ ?_
  · apply (le_trans (by linarith : preparedSlicedForecastPrimitiveCap ≤
      preparedSlicedForecastPrimitiveCap + 1)
      (Real.add_one_le_exp preparedSlicedForecastPrimitiveCap)).trans
    exact Real.exp_le_exp.mpr (by linarith)
  · calc
      2 * Real.exp cost ≤ Real.exp 1 * Real.exp cost :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (1 + cost) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (preparedSlicedForecastPrimitiveCap + cost + 1) :=
        Real.exp_le_exp.mpr (by linarith)

theorem preparedSlicedForecastChildSize_one_le (childLog : ℝ) :
    1 ≤ preparedSlicedForecastChildSize childLog := one_le_ceil_exp _

theorem preparedSlicedForecastChildSize_pos (childLog : ℝ) :
    0 < preparedSlicedForecastChildSize childLog :=
  preparedSlicedForecastChildSize_one_le childLog

theorem preparedSlicedForecastChildSize_lower (childLog : ℝ) :
    Real.exp childLog ≤ (preparedSlicedForecastChildSize childLog : ℝ) :=
  Nat.le_ceil _

theorem preparedSlicedForecastChildSize_upper {childLog : ℝ} (hchildLog : 0 ≤ childLog) :
    (preparedSlicedForecastChildSize childLog : ℝ) ≤ Real.exp (childLog + 1) :=
  ceil_exp_le_exp_add_one hchildLog

theorem preparedSlicedForecastPrimitiveChoices {cost childLog : ℝ}
    (hcost : 0 ≤ cost) (hchildLog : 0 ≤ childLog) :
    let C := preparedSlicedForecastPrimitiveCap
    let Ptail := preparedSlicedForecastTailCap cost
    let p := preparedSlicedForecastTailLog cost
    let δ := preparedSlicedForecastDensity cost
    let kernelV := preparedSlicedForecastKernelLog cost
    let Hchild := preparedSlicedForecastChildSize childLog
    1 ≤ Ptail ∧ C ≤ Ptail ∧ 2 * Real.exp cost ≤ Ptail ∧
      0 ≤ p ∧ 0 ≤ cost ∧ 0 ≤ kernelV ∧ 0 < δ ∧ δ⁻¹ ≤ Real.exp cost ∧
      Ptail ≤ Real.exp p ∧ 0 ≤ childLog + 1 ∧ 0 < Hchild ∧
      Real.exp childLog ≤ (Hchild : ℝ) ∧ (Hchild : ℝ) ≤ Real.exp (childLog + 1) := by
  exact ⟨preparedSlicedForecastTailCap_one_le cost,
    preparedSlicedForecastTailCap_primitive_le cost,
    preparedSlicedForecastTailCap_stride_le cost,
    preparedSlicedForecastTailLog_nonneg hcost, hcost,
    preparedSlicedForecastKernelLog_nonneg hcost,
    preparedSlicedForecastDensity_pos cost, (preparedSlicedForecastDensity_inv cost).le,
    preparedSlicedForecastTailCap_le_exp hcost, by linarith,
    preparedSlicedForecastChildSize_pos childLog,
    preparedSlicedForecastChildSize_lower childLog,
    preparedSlicedForecastChildSize_upper hchildLog⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastCommonFloorExponent
    (periodLog childLog cost comparisonLog : ℝ) : ℝ :=
  max 0 (max periodLog (max childLog (max (cost + 1) comparisonLog)))

noncomputable def preparedSlicedForecastCommonFloor
    (periodLog childLog cost comparisonLog : ℝ) : ℕ :=
  ⌈Real.exp (preparedSlicedForecastCommonFloorExponent
    periodLog childLog cost comparisonLog)⌉₊

theorem preparedSlicedForecastCommonFloor_bounds
    (periodLog childLog cost comparisonLog : ℝ) :
    let F := preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog
    let Lmin := preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog
    0 ≤ F ∧ 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (F + 1) ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro F Lmin
  have hF : 0 ≤ F := le_max_left _ _
  have hp : periodLog ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have hc : childLog ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs : cost + 1 ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have ha : comparisonLog ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hfloor : Real.exp F ≤ (Lmin : ℝ) := Nat.le_ceil _
  have hnat (a : ℝ) (haF : a ≤ F) (k : ℕ) (hk : (k : ℝ) ≤ Real.exp a) :
      k ≤ Lmin := by
    exact_mod_cast hk.trans ((Real.exp_le_exp.mpr haF).trans hfloor)
  refine ⟨hF, one_le_ceil_exp F, ceil_exp_le_exp_add_one hF, ?_, ?_, hnat _ hp, hnat _ ha⟩
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hc)
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc
      2 * Real.exp cost ≤ Real.exp 1 * Real.exp cost :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)
      _ = Real.exp (cost + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ Real.exp F := Real.exp_le_exp.mpr hs
      _ ≤ Lmin := hfloor

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastCommonFloorExponent_mono
    {periodLog childLog cost comparisonLog periodLog' childLog' cost' comparisonLog' : ℝ}
    (hperiod : periodLog ≤ periodLog') (hchild : childLog ≤ childLog')
    (hcost : cost ≤ cost') (hcomparison : comparisonLog ≤ comparisonLog') :
    preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog ≤
      preparedSlicedForecastCommonFloorExponent periodLog' childLog' cost' comparisonLog' := by
  unfold preparedSlicedForecastCommonFloorExponent
  exact max_le_max le_rfl (max_le_max hperiod
    (max_le_max hchild (max_le_max (by linarith only [hcost]) hcomparison)))

theorem preparedSlicedForecastCommonFloor_mono
    {periodLog childLog cost comparisonLog periodLog' childLog' cost' comparisonLog' : ℝ}
    (hperiod : periodLog ≤ periodLog') (hchild : childLog ≤ childLog')
    (hcost : cost ≤ cost') (hcomparison : comparisonLog ≤ comparisonLog') :
    preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤
      preparedSlicedForecastCommonFloor periodLog' childLog' cost' comparisonLog' := by
  unfold preparedSlicedForecastCommonFloor
  exact Nat.ceil_mono (Real.exp_le_exp.mpr
    (preparedSlicedForecastCommonFloorExponent_mono hperiod hchild hcost hcomparison))

theorem preparedSlicedForecastCommonFloor_mono_comparison
    (periodLog childLog cost : ℝ) {a b : ℝ} (hcomparison : a ≤ b) :
    preparedSlicedForecastCommonFloor periodLog childLog cost a ≤
      preparedSlicedForecastCommonFloor periodLog childLog cost b :=
  preparedSlicedForecastCommonFloor_mono le_rfl le_rfl le_rfl hcomparison

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

noncomputable def preparedSlicedForecastSourceLog (m M Jalloc : ℕ) (Ptest : ℝ) : ℝ :=
  2 + (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) ^ 2 +
    preparedSlicedForecastPrimitiveCap + max 0 Ptest

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_comparison_logs {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4)
    (Ptest : ℝ) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.pcap = preparedSlicedForecastPrimitiveCap ∧
      s.slicedComparisonSourceLog Ptest = preparedSlicedForecastSourceLog m M Jalloc Ptest := by
  simp only [ActualFixedSpatialForecastSetup.slicedComparisonSourceLog,
    preparedSlicedForecastSourceLog, preparedSlicedForecastPrimitiveCap, pow_two,
    preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth]
  trivial

end Erdos3.VectorPolynomial

end

end OAI
