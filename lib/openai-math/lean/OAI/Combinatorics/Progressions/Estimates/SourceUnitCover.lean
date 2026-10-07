import OAI.Combinatorics.Progressions.Dynamics.SymmetricUnitBudget
import OAI.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel
import OAI.Combinatorics.Progressions.Fourier.NaturalFrequencyMultiples
import OAI.Combinatorics.Progressions.Linear.SplitCoverProjection
import OAI.Combinatorics.Progressions.Polynomial.RaisedDegreeRank

namespace OAI

section

namespace Erdos3.RationalTorus

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def trivialMultidegreeFiltration (s : ℕ) (bound : σ → ℕ) :
    MultidegreeLieFiltration σ (Algebra 0) s bound where
  ordinary := trivialFiltration s
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  zero_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal _ _ := by
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]
  degree_eq _ := by
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]

noncomputable def trivialMultidegreeStructure (s : ℕ) (bound : σ → ℕ) :
    (trivialNilmanifold s).MultidegreeStructure bound := by
  letI := (basis 0).finiteDimensional_of_finite
  exact {
    filtration := trivialMultidegreeFiltration s bound
    ordinary := rfl
    basis := fun _ => Module.finBasis ℚ _
  }

theorem trivialMultidegreeStructure_complexity (s : ℕ) (bound : σ → ℕ) {p : ℝ}
    (hp : 0 ≤ p) : (trivialMultidegreeStructure s bound).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s hp, ?_⟩
  intro a j k
  exact Fin.elim0 k

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure UnitVerticalObservable (D : RationalFilteredNilmanifold L s d)
    (T : Subgroup D.RealGroup) (I : Type*) [Fintype I] (p : ℝ) where
  observable : I → D.Space → ℂ
  unit : ∀ x, ∑ i, ‖observable i x‖ ^ 2 = 1
  norm : ∀ i x, ‖observable i x‖ ≤ 1
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp p
  lipschitz : letI := D.metricSpace; ∀ i, LipschitzWith lipBound (observable i)
  frequency : L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (D.basis i)) ≤ p
  vertical : ∀ i z, z ∈ T → ∀ x, observable i (z • x) =
    CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
      observable i x
  integral : ∀ z : D.RealGroup, z ∈ T → z ∈ D.realLattice →
    ∃ n : ℤ, realifyFunctional frequency z.coord = n

namespace UnitVerticalObservable

variable {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p q : ℝ}

noncomputable def mono (V : D.UnitVerticalObservable T I p) (hpq : p ≤ q) :
    D.UnitVerticalObservable T I q :=
  { V with
    lip_bound := V.lip_bound.trans (Real.exp_le_exp.mpr hpq)
    height := fun i => (V.height i).trans hpq }

noncomputable def constOne (D : RationalFilteredNilmanifold L s d) (T : Subgroup D.RealGroup)
    (hp : 0 ≤ p) : D.UnitVerticalObservable T (Fin 1) p where
  observable _ _ := 1
  unit _ := by simp
  norm _ _ := by simp
  lipBound := 0
  lip_bound := (Real.exp_pos p).le
  lipschitz := by
    let := D.metricSpace
    exact fun _ => LipschitzWith.const 1
  frequency := 0
  height _ := by simpa [rationalLogHeight] using hp
  vertical _ _ _ _ := by simp only [realifyFunctional_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul]
  integral _ _ _ := ⟨0, by simp only [realifyFunctional_zero, Int.cast_zero]⟩

end UnitVerticalObservable

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem frozen_quotient_map_smul {G : Type*} [Group G]
    (Γ Λ : Subgroup G) (a r : G) (f : G ⧸ Γ → G ⧸ Λ)
    (hf : ∀ x : G, f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * r))
    (z : G) (hz : Commute z a) (x : G ⧸ Γ) : f (z • x) = z • f x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change f (QuotientGroup.mk (z * x)) = z • f (QuotientGroup.mk x)
    rw [hf, hf]
    change (QuotientGroup.mk (a * (z * x) * r) : G ⧸ Λ) = QuotientGroup.mk (z * (a * x * r))
    congr 1
    calc
      _ = (a * z) * x * r := by group
      _ = (z * a) * x * r := by rw [hz.eq]
      _ = _ := by group

namespace RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

namespace DegreeRankStructure

noncomputable def withLattice (R : D.DegreeRankStructure r)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    (D.withLattice Λ N hN hin hout).DegreeRankStructure r where
  filtration := R.filtration
  associated := R.associated
  basis := R.basis

theorem withLattice_complexity (R : D.DegreeRankStructure r)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p P : ℝ} (hR : R.ComplexityLE p) (hpP : p ≤ P)
    (hQ : (D.withLattice Λ N hN hin hout).GeometryComplexityLE P) :
    (R.withLattice Λ N hN hin hout).ComplexityLE P :=
  ⟨hQ, fun i j a k => (hR.2 i j a k).trans hpP⟩

theorem top_realSubgroup_commute (R : D.DegreeRankStructure r)
    {z : D.RealGroup} (hz : z ∈ R.realSubgroup s r) (x : D.RealGroup) : Commute z x := by
  apply commute_of_lie_eq_zero
  exact D.filtration.realification.top_layer_central (R.realSubgroup_le_degree s r hz) x.coord

end DegreeRankStructure

variable {I : Type*} [Fintype I]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace UnitVerticalObservable

noncomputable def frozenCover (R : D.DegreeRankStructure r) {p P : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
    (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    (a u : D.RealGroup) (f : (D.withLattice Λ N hN hin hout).Space → D.Space)
    (hf : ∀ x : D.RealGroup, f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * u))
    (K : ℝ≥0)
    (hLip : letI := (D.withLattice Λ N hN hin hout).metricSpace;
      letI := D.metricSpace; LipschitzWith K f)
    (hpP : p ≤ P) (hK : (V.lipBound * K : ℝ≥0) ≤ Real.exp P) :
    (D.withLattice Λ N hN hin hout).UnitVerticalObservable
      ((R.withLattice Λ N hN hin hout).realSubgroup s r) I P where
  observable i x := V.observable i (f x)
  unit x := V.unit (f x)
  norm i x := V.norm i (f x)
  lipBound := V.lipBound * K
  lip_bound := hK
  lipschitz := by
    let := (D.withLattice Λ N hN hin hout).metricSpace
    let := D.metricSpace
    exact fun i => (V.lipschitz i).comp hLip
  frequency := V.frequency
  height i := (V.height i).trans hpP
  vertical i z hz x := by
    rw [frozen_quotient_map_smul _ _ a u f hf z (R.top_realSubgroup_commute hz a)]
    exact V.vertical i z hz (f x)
  integral z hz hlat := by
    have hsub : (D.withLattice Λ N hN hin hout).realLattice ≤ D.realLattice := Subgroup.map_mono hΛ
    exact V.integral z hz (hsub hlat)

end UnitVerticalObservable
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal TensorProduct

noncomputable def invariantVerticalBudget (m : ℕ) (p : ℝ) : ℝ :=
  symmetricUnitBudget m (2 * p) + p + m + 1

namespace RationalFilteredNilmanifold.UnitVerticalObservable

variable {Γ I L : Type*} [Group Γ] [Fintype Γ] [Fintype I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  [MulAction Γ D.Space]

theorem exists_invariant (V : D.UnitVerticalObservable T I p) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp p)
    (hact : letI := D.metricSpace; ∀ a : Γ, LipschitzWith A (fun x : D.Space => a • x))
    (hcomm : ∀ (a : Γ) (z : D.RealGroup), z ∈ T → ∀ x : D.Space,
      a • (z • x) = z • (a • x)) :
    ∃ W : D.UnitVerticalObservable T (SymmetricEvaluationIndex (Fintype.card Γ) I)
        (invariantVerticalBudget (Fintype.card Γ) p),
      W.frequency = Fintype.card Γ • V.frequency ∧
      (∀ (a : Γ) k x, W.observable k (a • x) = W.observable k x) ∧
      (Fintype.card (SymmetricEvaluationIndex (Fintype.card Γ) I) : ℝ) ≤
        Real.exp (invariantVerticalBudget (Fintype.card Γ) p) := by
  let := D.metricSpace
  let m := Fintype.card Γ
  have hp2 : 0 ≤ 2 * p := by positivity
  have hbudget : 0 ≤ symmetricUnitBudget m (2 * p) := by
    unfold symmetricUnitBudget
    positivity
  have hbase : symmetricUnitBudget m (2 * p) ≤ invariantVerticalBudget m p := by
    unfold invariantVerticalBudget
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hfreq : p + m + 1 ≤ invariantVerticalBudget m p := by
    unfold invariantVerticalBudget
    linarith
  have hIA : (Fintype.card I : ℝ) ≤ Real.exp (2 * p) :=
    hI.trans (Real.exp_le_exp.mpr (by linarith))
  have hKA : ((V.lipBound * A : ℝ≥0) : ℝ) ≤ Real.exp (2 * p) := by
    simpa only [NNReal.coe_mul, ← Real.exp_add, two_mul] using
      mul_le_mul V.lip_bound hA A.coe_nonneg (Real.exp_pos _).le
  obtain ⟨hcard, hLip⟩ := symmetricUnitBudget_bounds m (Fintype.card I) (V.lipBound * A) hp2 hIA hKA
  obtain ⟨g, hgunit, hgnorm, hglip, hginv, hgphase⟩ :=
    exists_invariant_unit_family (Γ := Γ) V.observable V.lipschitz V.unit hact
  refine ⟨{
    observable := g
    unit := hgunit
    norm := hgnorm
    lipBound := symmetricUnitFamilyLip m (Fintype.card I) (V.lipBound * A)
    lip_bound := hLip.trans (Real.exp_le_exp.mpr hbase)
    lipschitz := hglip
    frequency := m • V.frequency
    height := ?_
    vertical := ?_
    integral := ?_
  }, rfl, hginv, ?_⟩
  · intro i
    exact (show rationalLogHeight ((m • V.frequency) (D.basis i)) ≤ p + m + 1 by
      simpa only [LinearMap.smul_apply, nsmul_eq_mul] using
        rationalLogHeight_nat_mul m (V.height i)).trans hfreq
  · intro k z hz x
    have h := hgphase (z • x) x
      (character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle))
      (norm_character _) (fun a j => by rw [hcomm a z hz, V.vertical j z hz]) k
    simpa only [realifyFunctional_nsmul, AddCircle.coe_nsmul, character_nsmul] using h
  · intro z hz hL
    obtain ⟨n, hn⟩ := V.integral z hz hL
    refine ⟨(m : ℤ) * n, ?_⟩
    rw [realifyFunctional_nsmul, hn]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  · rw [symmetricEvaluationIndex_card]
    exact hcard.trans (Real.exp_le_exp.mpr hbase)

end RationalFilteredNilmanifold.UnitVerticalObservable

theorem exists_invariantVertical_cost (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → invariantVerticalBudget m p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C (2 * m + 2) * (2 * X + 1) + Polynomial.C (symmetricUnitConstant m) +
    X + Polynomial.C m + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [X, P, invariantVerticalBudget, symmetricUnitBudget] using hbound p hp

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeMultidegreeNilcharacter {σ : Type*} [Fintype σ] (bound : σ → ℕ) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L (∑ i, bound i) dim
  multi : model.MultidegreeStructure bound
  complexity : multi.ComplexityLE p
  orbit : multi.filtration.realification.PolynomialOrbit
  outputDim : ℕ
  output_pos : 0 < outputDim
  output_bound : (outputDim : ℝ) ≤ Real.exp p
  vertical : model.UnitVerticalObservable (multi.realSubgroup bound) (Fin outputDim) p

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def eval (i : Fin W.outputDim) (x : σ → ℤ) : ℂ :=
  W.vertical.observable i (QuotientGroup.mk
    (W.multi.filtration.realification.polynomialOrbitEval x W.orbit))

noncomputable def evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (x : σ → ZMod N) : ℂ :=
  W.eval i (fun j => ((x j).val : ℤ))

theorem unit_eval (x : σ → ℤ) : ∑ i, ‖W.eval i x‖ ^ 2 = 1 := W.vertical.unit _

theorem norm_eval (i : Fin W.outputDim) (x : σ → ℤ) : ‖W.eval i x‖ ≤ 1 := W.vertical.norm i _

noncomputable def mono (hpq : p ≤ q) : NativeMultidegreeNilcharacter bound q :=
  { W with
    complexity := W.complexity.mono W.multi hpq
    output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
    vertical := W.vertical.mono hpq }

theorem mono_eval (hpq : p ≤ q) (i : Fin W.outputDim) (x : σ → ℤ) :
    (W.mono hpq).eval i x = W.eval i x := rfl

noncomputable def constOne (bound : σ → ℕ) (hp : 0 ≤ p) :
    NativeMultidegreeNilcharacter bound p where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold (∑ i, bound i)
  multi := RationalTorus.trivialMultidegreeStructure (∑ i, bound i) bound
  complexity := RationalTorus.trivialMultidegreeStructure_complexity _ _ hp
  orbit := 1
  outputDim := 1
  output_pos := by omega
  output_bound := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  vertical := RationalFilteredNilmanifold.UnitVerticalObservable.constOne _ _ hp

@[simp] theorem constOne_eval (bound : σ → ℕ) (hp : 0 ≤ p) (i : Fin 1) (x : σ → ℤ) :
    (constOne bound hp).eval i x = 1 := rfl

@[simp] theorem constOne_evalCyclic (bound : σ → ℕ) (hp : 0 ≤ p) (N : ℕ) [NeZero N]
    (i : Fin 1) (x : σ → ZMod N) : (constOne bound hp).evalCyclic N i x = 1 := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M I : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup E.RealGroup} {p q : ℝ} (V : E.UnitVerticalObservable T I p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (S : Subgroup D.RealGroup)
  (hS : S ≤ T.comap (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (K : ℝ≥0)
  (hLip : letI := D.metricSpace; letI := E.metricSpace;
    LipschitzWith K (D.nativeSpaceMap E φ hφ))
  (hK : ((V.lipBound * K : ℝ≥0) : ℝ) ≤ Real.exp q)
  (hfreq : ∀ i, rationalLogHeight (V.frequency (φ (D.basis i))) ≤ q)

noncomputable def pullback : D.UnitVerticalObservable S I q where
  observable i x := V.observable i (D.nativeSpaceMap E φ hφ x)
  unit x := V.unit (D.nativeSpaceMap E φ hφ x)
  norm i x := V.norm i (D.nativeSpaceMap E φ hφ x)
  lipBound := V.lipBound * K
  lip_bound := hK
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact fun i => (V.lipschitz i).comp hLip
  frequency := V.frequency.comp φ.toLinearMap
  height := hfreq
  vertical i z hz x := by
    rw [D.nativeSpaceMap_smul E φ hφ z x, realifyFunctional_comp]
    exact V.vertical i
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z) (hS hz) _
  integral z hz hlat := by
    obtain ⟨n, hn⟩ := V.integral
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z)
      (hS hz) ((realificationMap_subgroup φ D.lattice E.lattice hφ) hlat)
    refine ⟨n, ?_⟩
    rw [realifyFunctional_comp]
    exact hn

theorem pullback_frequency :
    (V.pullback φ hφ S hS K hLip hK hfreq).frequency = V.frequency.comp φ.toLinearMap := rfl

theorem pullback_observable_mk (i : I) (x : D.RealGroup) :
    (V.pullback φ hφ S hS K hLip hK hfreq).observable i (QuotientGroup.mk x) =
      V.observable i (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) := rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
  (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
  (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m)

noncomputable def onSublattice :
    (D.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((R.withLattice Λ m hm hin hout).realSubgroup s r) I p where
  observable i := V.observable i ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  unit x := V.unit _
  norm i x := V.norm i _
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := fun i => sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout)
    hΛ rfl (V.observable i) (V.lipschitz i)
  frequency := V.frequency
  height := V.height
  vertical i z hz x := by
    induction x using Quotient.inductionOn with
    | h x => exact V.vertical i z hz (QuotientGroup.mk x)
  integral z hz hlat := V.integral z hz (Subgroup.map_mono hΛ hlat)

theorem onSublattice_frequency :
    (V.onSublattice R Λ hΛ m hm hin hout).frequency = V.frequency := rfl

theorem onSublattice_lipBound :
    (V.onSublattice R Λ hΛ m hm hin hout).lipBound = V.lipBound := rfl

theorem onSublattice_observable_mk (i : I) (x : D.RealGroup) :
    (V.onSublattice R Λ hΛ m hm hin hout).observable i (QuotientGroup.mk x) =
      V.observable i (QuotientGroup.mk x) := rfl

theorem onSublattice_orbit_eval {σ : Type*} (w : σ → ℕ)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) (x : σ → ℤ) :
    (V.onSublattice R Λ hΛ m hm hin hout).observable i (QuotientGroup.mk
      ((D.withLattice Λ m hm hin hout).filtration.realification.polynomialOrbitEval w x g)) =
      V.observable i (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) := rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_source_unit_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M I : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s t d e r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
      0 ≤ p → R.ComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (R.withLattice Λ N hN hin hout).ComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) ∧
          ∀ V : D.UnitVerticalObservable (R.realSubgroup s r) I p,
            ∃ U : (D.withLattice Λ N hN hin hout).UnitVerticalObservable
                ((R.withLattice Λ N hN hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ U.lipBound = V.lipBound ∧
              ∀ i x, U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk x) := by
  obtain ⟨C, hC, hcover⟩ := exists_native_source_cover
  refine ⟨C, hC, ?_⟩
  intro L M I _ _ _ _ _ _ _ _ _ s t d e r D R E φ p hp hR hE hentries
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hpC : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + C) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ C)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hgeometry, hmap⟩ :=
    hcover D E φ hp hR.1 hE hentries
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout,
    R.withLattice_complexity Λ N hN hin hout hR hpC hgeometry, hmap, ?_⟩
  intro V
  exact ⟨(V.onSublattice R Λ hΛ N hN hin hout).mono hpC, rfl, rfl, fun _ _ => rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
