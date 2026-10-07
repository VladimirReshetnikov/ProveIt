import OAI.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong

namespace OAI

section

universe u v w₀ w₁ w₂

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

def nativeOptionTargetObservableBudget (p : ℝ) : ℝ :=
  (p + 3) ^ 2 + 2 + 2 * ((p + 3) ^ 2 + 4) ^ 2

variable {Pivot : Type v} {LQ : Type u} {LS : Type w₀} {Param : Type w₁} {σ : Type w₂}
    [Fintype Pivot] {LP : Pivot → Type u}
    [LieRing LQ] [LieAlgebra ℚ LQ] [LieRing LS] [LieAlgebra ℚ LS]
    [∀ j, LieRing (LP j)] [∀ j, LieAlgebra ℚ (LP j)]
    {s t dQ dS : ℕ} {dp : Pivot → ℕ}
    (Q : RationalFilteredNilmanifold LQ s dQ)
    (partners : ∀ j, RationalFilteredNilmanifold (LP j) s (dp j))
    {Source : RationalFilteredNilmanifold LS t dS}
    {ψ : LS →ₗ⁅ℚ⁆ (∀ i : Option Pivot, optionLieSpace LQ LP i)}
    [TopologicalSpace (ℝ ⊗[ℚ] LQ)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LQ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LQ)] [T2Space (ℝ ⊗[ℚ] LQ)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] LP j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] LP j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] LP j)] [∀ j, T2Space (ℝ ⊗[ℚ] LP j)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]

theorem AdaptedMapGeometryData.optionTarget_observable_regularity
    {p0 q : ℝ}
    (geometry : Source.AdaptedMapGeometryData (optionProduct Q partners) ψ ((p0 + 3) ^ 2) q)
    {w : σ → ℕ} (descended : Param → Q.Niltest w)
    (hp0 : 0 ≤ p0) (hQ : Q.GeometryComplexityLE p0)
    (hunit : ∀ x, (descended x).UnitIntervalValued)
    (hcomplexity : ∀ x, (descended x).ComplexityLE p0) :
    (∀ x (y : geometry.target.model.Space),
      (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).im = 0 ∧
      0 ≤ (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).re ∧
      (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).re ≤ 1) ∧
    (∀ x (y : geometry.target.model.Space),
      ‖optionOriginalObservable Q partners (fun x => (descended x).observable) x y‖ ≤ 1) ∧
    (∀ x, letI := geometry.target.model.metricSpace;
      LipschitzWith ⟨Real.exp (nativeOptionTargetObservableBudget p0), Real.exp_nonneg _⟩
        (fun y : geometry.target.model.Space =>
          optionOriginalObservable Q partners (fun x => (descended x).observable) x y)) ∧
    ∀ (sites : Set Param) (entropy : ℝ → ℝ),
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ entropy η ∧ ∃ rep : Fin n → {x : Param // x ∈ sites},
          ∀ x ∈ sites, ∃ i, ∀ y,
            ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ entropy η ∧ ∃ rep : Fin n → {x : Param // x ∈ sites},
          ∀ x ∈ sites, ∃ i, ∀ y : geometry.target.model.Space,
            ‖optionOriginalObservable Q partners (fun x => (descended x).observable) x y -
              optionOriginalObservable Q partners (fun x => (descended x).observable)
                (rep i).val y‖ ≤ η := by
  classical
  let ℓ : ℝ≥0 := ⟨Real.exp p0, Real.exp_nonneg _⟩
  have hLip (x : Param) : letI := Q.metricSpace; LipschitzWith ℓ (descended x).observable := by
    let := Q.metricSpace
    apply (descended x).lipschitz.weaken
    change ((descended x).lipBound : ℝ) ≤ Real.exp p0
    have hb := (descended x).observable_budget (hcomplexity x)
    linarith [(descended x).normBound.coe_nonneg]
  let jointGeo := (p0 + 3) ^ 2
  let r := jointGeo + 2
  have hjoint : 0 ≤ jointGeo := by dsimp [jointGeo]; positivity
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p0 ≤ r := by dsimp [r, jointGeo]; nlinarith
  have htotal : (Fintype.card (Σ i : Option Pivot, Fin (optionDimension dQ dp i)) : ℝ) ≤
      jointGeo := by
    simpa only [finrank_eq_card_basis (optionProduct Q partners).basis, Fintype.card_fin] using
      geometry.target_dimension
  have hH : (⌈Real.exp (jointGeo + 1)⌉₊ : ℝ) ≤ Real.exp r := by
    simpa only [r, show jointGeo + 1 + 1 = jointGeo + 2 by ring] using
      ceil_exp_le_exp_add_one (show 0 ≤ jointGeo + 1 by linarith)
  have hbound := optionOriginalAdaptedLipschitzBound_le_exp Q partners ℓ
    ⌈Real.exp (jointGeo + 1)⌉₊ hr (Real.exp_le_exp.mpr hpr) (hQ.1.trans hpr)
    (htotal.trans (by dsimp [r]; linarith)) hH
  refine ⟨optionOriginalObservable_adapted_unit_interval Q partners
      (fun x => (descended x).observable) geometry.target hunit,
    fun x y => (hunit x).norm_le_one (optionOriginalSpaceProjection Q partners y), ?_, ?_⟩
  · intro x
    let := geometry.target.model.metricSpace
    have hl := optionOriginalObservable_adapted_lipschitz_of_logHeight Q partners
      (fun x => (descended x).observable) geometry.target ℓ (jointGeo + 1)
      geometry.target_forward hLip x
    apply hl.weaken
    change (optionOriginalAdaptedLipschitzBound (L₀ := LQ) (L := LP)
      (d₀ := dQ) (d := dp) ℓ ⌈Real.exp (jointGeo + 1)⌉₊ : ℝ) ≤
        Real.exp (nativeOptionTargetObservableBudget p0)
    convert hbound using 1
    unfold nativeOptionTargetObservableBudget r jointGeo
    congr 1
    ring
  · intro sites entropy hnets
    exact optionOriginalObservable_adapted_member_nets Q partners
      (fun x => (descended x).observable) geometry.target sites entropy hnets

end Erdos3.RationalFilteredNilmanifold

end

end OAI
