import OAI.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

noncomputable def dropTopMap : (D.dropTop hD).Space → D.Space :=
  cosetMap (D.dropTop hD).realLattice D.realLattice
    (realificationMap (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L) (D.dropTop hD).lattice D.lattice
      (D.dropTop_lattice_back hD))

theorem dropTopMap_mk (x : (D.dropTop hD).RealGroup) :
    D.dropTopMap hD (QuotientGroup.mk x) =
      QuotientGroup.mk (changeStep (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot
        D.filtration.realification.lowerCentralSeries_eq_bot x) := by
  change QuotientGroup.mk (realificationMap
    (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) = _
  rw [realificationMap_id_eq_changeStep]

theorem dropTopMap_surjective : Function.Surjective (D.dropTopMap hD) := by
  apply cosetMap_surjective
  rw [realificationMap_id_eq_changeStep]
  exact (changeStep _ _).surjective

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem dropTopMap_lipschitz :
    letI := (D.dropTop hD).metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (D.dropTopMap hD) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1
      (realificationMap (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
    rw [realificationMap_id_eq_changeStep]
    exact lipschitz_changeStep (D.basis.baseChange ℝ) _ _
  exact lipschitz_cosetMap (D.dropTop hD).realLattice D.realLattice
    (D.dropTop hD).realLattice_closed_discrete.1 D.realLattice_closed_discrete.1 _ _ hLip

end Metric

noncomputable def dropTopRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.dropTop hD).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

theorem dropTopMap_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.dropTopMap hD (QuotientGroup.mk
      ((D.dropTop hD).filtration.realification.polynomialOrbitEval w x (D.dropTopRealOrbit hD g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.dropTopMap_mk]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L (s + 1) d} {w : σ → ℕ}

noncomputable def dropTop (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥) :
    (D.dropTop hD).Niltest w where
  orbit := D.dropTopRealOrbit hD T.orbit
  observable := T.observable ∘ D.dropTopMap hD
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := (D.dropTop hD).metricSpace
    simpa only [mul_one] using T.lipschitz.comp (D.dropTopMap_lipschitz hD)

theorem dropTop_eval (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥) (x : σ → ℤ) :
    (T.dropTop hD).eval x = T.eval x :=
  congrArg T.observable (D.dropTopMap_orbit hD T.orbit x)

theorem dropTop_evalCyclic (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) : (T.dropTop hD).evalCyclic N x = T.evalCyclic N x :=
  T.dropTop_eval hD _

theorem dropTop_complexity (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.dropTop hD).ComplexityLE p :=
  ⟨D.dropTop_geometry hD hT.1, hT.2⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NativeDegreeRankFamily

open scoped NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def component (i : Fin W.outputDim) (a : A) :
    W.model.Niltest (fun _ : Unit => 1) where
  orbit := W.orbit a
  observable := W.vertical.observable i
  normBound := 1
  lipBound := W.vertical.lipBound
  norm_le := W.vertical.norm i
  lipschitz := W.vertical.lipschitz i

theorem component_eval (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.component i a).eval (fun _ => n) = W.eval i a n := rfl

theorem component_evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) :
    (W.component i a).evalCyclic N (fun _ => n) = W.evalCyclic N i a n := rfl

theorem component_complexity (hp : 0 ≤ p) (i : Fin W.outputDim) (a : A) :
    (W.component i a).ComplexityLE (p + 4) := by
  refine ⟨W.complexity.1.mono W.model (by linarith), ?_⟩
  have h := niltest_log_bound_of_exp (1 : ℝ≥0) W.vertical.lipBound
    (a := 0) (b := p) (by norm_num) hp (by simp) W.vertical.lip_bound
  simpa only [component, zero_add] using h

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3.NativeDegreeRankFamily

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily (s + 1) 0 A p)

theorem rankZero_top_eq_bot : W.model.filtration.layer (s + 1) = ⊥ := by
  rw [← W.rank.associated]
  exact W.rank.filtration.rank_zero_top_eq_bot

noncomputable def lowerComponent (i : Fin W.outputDim) (a : A) :
    (W.model.dropTop W.rankZero_top_eq_bot).Niltest (fun _ : Unit => 1) :=
  (W.component i a).dropTop W.rankZero_top_eq_bot

theorem lowerComponent_eval (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.lowerComponent i a).eval (fun _ => n) = W.eval i a n := by
  rw [lowerComponent, RationalFilteredNilmanifold.Niltest.dropTop_eval, W.component_eval]

theorem lowerComponent_evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) :
    (W.lowerComponent i a).evalCyclic N (fun _ => n) = W.evalCyclic N i a n :=
  W.lowerComponent_eval i a _

theorem lowerComponent_complexity (hp : 0 ≤ p) (i : Fin W.outputDim) (a : A) :
    (W.lowerComponent i a).ComplexityLE (p + 4) :=
  (W.component i a).dropTop_complexity W.rankZero_top_eq_bot (W.component_complexity hp i a)

end Erdos3.NativeDegreeRankFamily

end

end OAI
