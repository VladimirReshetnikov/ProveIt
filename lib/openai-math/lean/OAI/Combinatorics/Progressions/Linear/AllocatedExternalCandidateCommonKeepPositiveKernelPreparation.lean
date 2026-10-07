import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrecenterPaths
import OAI.Combinatorics.Progressions.Linear.AllocatedExternalCandidateNormalizedKernelRestoration

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure PrecenterKernelSelection
    {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    (early : ExternalFamilyPrecenterProjectionData T p q)
    (top : Submodule ℚ L) (htop : top ≤ D.filtration.layer s)
    (hpos : 0 < A.law.mass P.productive) where
  code : Fin (finrank ℚ top) → Option early.Freq
  tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)
  test_bounds : ∀ x, (tests x).UnitIntervalValued ∧ (tests x).ComplexityLE q ∧
    (tests x).orbit = (T x).orbit
  identity : ∀ x, tests x = (T x).kernelProjection (frequencyCodeKernel top early.eta code)
    ((finiteFrequencyKernel_le top _ _).trans htop)
  invariant : ∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel top early.eta code).baseChange ℝ →
    ∀ x, (tests a).observable (z • x) = (tests a).observable x
  retained : Finset A.Path
  subset : retained ⊆ P.productive
  mass : A.law.mass P.productive * Real.exp (-q) ≤ A.law.mass retained
  pivots : ∀ a ∈ retained, ∀ i f, code i = some f → Real.exp (-q) <
    ‖(P.precenterChart hpos a).localLaw.complexMean (fun site =>
      weight (A.physical (P.precenterChart hpos a).path site) *
        (early.U f (A.physical (P.precenterChart hpos a).path site)).observable
          ((P.precenterCandidate hpos a).siteValue site))‖
  scores : ∀ a ∈ retained, Real.exp (-q) ≤
    (P.precenterCandidate hpos a).score (fun x => (tests x).observable) weight

theorem exists_precenterKernelSelection
    {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    (early : ExternalFamilyPrecenterProjectionData T p q)
    (top : Submodule ℚ L) (htop : top ≤ D.filtration.layer s)
    (hpos : 0 < A.law.mass P.productive)
    (hξ1 : ξ ≤ 1)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hobservable : ∀ x, (T x).observable = observable x) :
    Nonempty (P.PrecenterKernelSelection early top htop hpos) := by
  obtain ⟨code, tests, retained, htests, hidentity, hinvariant, hsub, hmass, hlocal⟩ :=
    early.select top htop A.law P.productive
      (fun a => (P.precenterChart hpos a).localLaw)
      (fun a => A.physical (P.precenterChart hpos a).path)
      (fun a => (P.precenterCandidate hpos a).siteValue)
      (fun a site => weight (A.physical (P.precenterChart hpos a).path site))
      (fun a site => hweight _ (A.physical_mem_integerBox hξ1 _ _)) (by
        intro a ha
        have hs := hscore.trans (P.precenterCandidate_score hpos a)
        rw [← (P.precenterCandidate hpos a).localLaw_score observable weight] at hs
        simpa only [hobservable] using hs)
  refine ⟨{
    code := code
    tests := tests
    test_bounds := htests
    identity := hidentity
    invariant := hinvariant
    retained := retained
    subset := hsub
    mass := hmass
    pivots := fun a ha => (hlocal a ha).1
    scores := ?_ }⟩
  intro a ha
  exact ((hlocal a ha).2).trans_eq
    ((P.precenterCandidate hpos a).localLaw_score (fun x => (tests x).observable) weight)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

noncomputable def problem :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked
      (fun x => (selected.tests x).observable) weight cost
      (A.law.mass P.productive * Real.exp (-q)) (Real.exp (-q)) :=
  P.restrictObservable (fun x => (selected.tests x).observable) selected.retained selected.subset
    selected.mass (fun a => by
      rw [← P.precenterCandidate_score_mem_eq hpos a.val (selected.subset a.property)]
      exact selected.scores a.val a.property)

theorem positive_mass : 0 < A.law.mass selected.retained :=
  (mul_pos hpos (Real.exp_pos _)).trans_le selected.mass

@[simp] theorem problem_productive : selected.problem.productive = selected.retained := rfl

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def positiveKernelPreparationExponent : ℕ :=
  Classical.choose (exists_externalFamilyPrecenterProjectionData.{0, 0, 0})

theorem positiveKernelPreparationExponent_ge_two :
    2 ≤ positiveKernelPreparationExponent :=
  (Classical.choose_spec (exists_externalFamilyPrecenterProjectionData.{0, 0, 0})).1

noncomputable def positiveKernelPreparationParameter (p : ℝ) : ℝ :=
  (p + 5) ^ positiveKernelPreparationExponent

noncomputable def positiveKernelPreparationBinLog (p : ℝ) (e : ℕ) : ℝ :=
  (2 * p + positiveKernelPreparationParameter p + 5 + e) ^ e

structure PositiveKernelPreparation (p : ℝ) (e : ℕ) where
  positive_mass : 0 < A.law.mass P.productive
  tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)
  tests_observable : ∀ x, (tests x).observable = observable x
  tests_unit : ∀ x, (tests x).UnitIntervalValued
  tests_complexity : ∀ x, (tests x).ComplexityLE (p + 3)
  early : ExternalFamilyPrecenterProjectionData tests (p + 3)
    (positiveKernelPreparationParameter p)
  selected : P.PrecenterKernelSelection early
    (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) inf_le_left positive_mass
  binCount : ℕ
  binCount_pos : 0 < binCount
  representative : Fin binCount → integerBox N
  net : ∀ x : integerBox N, ∃ i, ∀ y,
    ‖(tests x.val).observable y - (tests (representative i).val).observable y‖ ≤
      Real.exp (-((p + 3) + positiveKernelPreparationParameter p + 2))
  binCard : (binCount : ℝ) ≤ Real.exp (positiveKernelPreparationBinLog p e)

theorem exists_positiveKernelPreparation
    (p : ℝ) (e : ℕ) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hξ1 : ξ ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ η) :
    Nonempty (P.PositiveKernelPreparation p e) := by
  classical
  let := D.metricSpace
  have hcap (x : X → ℤ) (y : D.Space) : ‖observable x y‖ ≤ 1 := by
    simpa only [positiveClip_eq_self _ (hpositive x y)] using
      norm_positiveClip_le_one (observable x y)
  let tests (x : X → ℤ) : D.Niltest (fullTaggedVariableWeight (X := X) J) :=
    D.externalNetNiltest (observable x) ℓ (hcap x) (hLip x) 1
  have hunit (x : X → ℤ) : (tests x).UnitIntervalValued := hpositive x
  have hcomplexity (x : X → ℤ) : (tests x).ComplexityLE (p + 3) :=
    D.externalNetNiltest_complexity (observable x) ℓ (hcap x) (hLip x) 1 hp hD hℓ
  have hp3 : 0 ≤ p + 3 := by linarith
  have hpp3 : p ≤ p + 3 := by linarith
  obtain ⟨early⟩ := (Classical.choose_spec
    (exists_externalFamilyPrecenterProjectionData.{0, 0, 0})).2 tests (p + 3) hp3
      (hD.mono D hpp3) hunit hcomplexity
  have hq : positiveKernelPreparationParameter p =
      (p + 3 + 2) ^ positiveKernelPreparationExponent := by
    simp only [positiveKernelPreparationParameter, show p + 3 + 2 = p + 5 by ring]
  change ExternalFamilyPrecenterProjectionData tests (p + 3)
    ((p + 3 + 2) ^ positiveKernelPreparationExponent) at early
  rw [← hq] at early
  have hpos : 0 < A.law.mass P.productive :=
    (Real.exp_pos _).trans_le (hmass.trans P.mass)
  obtain ⟨selected⟩ := P.exists_precenterKernelSelection early
    (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) inf_le_left hpos hξ1
    (fun x _ => (hweight x).trans (Real.exp_le_exp.mpr hpp3))
    ((Real.exp_le_exp.mpr (neg_le_neg hpp3)).trans hscore) (fun _ => rfl)
  let η := Real.exp (-((p + 3) + positiveKernelPreparationParameter p + 2))
  have hη : 0 < η := Real.exp_pos _
  have hq0 : 0 ≤ positiveKernelPreparationParameter p := by
    unfold positiveKernelPreparationParameter
    positivity
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨count, hcount, centers, hcenters⟩ := hnet η hη hη1
  have hcountPos : 0 < count := by
    have hzero : (0 : X → ℤ) ∈ integerBox N := by
      apply (mem_integerBox N _).mpr
      intro x
      change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < (N x : ℤ)
      exact ⟨le_rfl, by exact_mod_cast A.size_pos x⟩
    obtain ⟨i, _⟩ := hcenters 0 hzero
    exact Nat.zero_lt_of_lt i.isLt
  have hlog : Real.log (1 / η) = (p + 3) + positiveKernelPreparationParameter p + 2 := by
    dsimp [η]
    rw [one_div, ← Real.exp_neg, Real.log_exp]
    ring
  have hbin : (count : ℝ) ≤ Real.exp (positiveKernelPreparationBinLog p e) := by
    rw [hlog] at hcount
    convert hcount using 1
    unfold positiveKernelPreparationBinLog
    congr 2
    ring
  exact ⟨{
    positive_mass := hpos
    tests := tests
    tests_observable := fun _ => rfl
    tests_unit := hunit
    tests_complexity := hcomplexity
    early := early
    selected := selected
    binCount := count
    binCount_pos := hcountPos
    representative := centers
    net := fun x => hcenters x.val x.property
    binCard := hbin }⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

theorem positiveKernelPreparationParameter_ge_input {p : ℝ} (hp : 0 ≤ p) :
    p + 3 ≤ positiveKernelPreparationParameter p := by
  have hC := positiveKernelPreparationExponent_ge_two
  have hbase : 1 ≤ p + 5 := by linarith
  have hself : p + 5 ≤ (p + 5) ^ positiveKernelPreparationExponent := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase
      (by omega : 1 ≤ positiveKernelPreparationExponent)
  unfold positiveKernelPreparationParameter
  linarith

theorem positiveKernelPreparationParameter_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ positiveKernelPreparationParameter p := by
  have := positiveKernelPreparationParameter_ge_input hp
  linarith

theorem positiveKernelPreparationBinLog_nonneg {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    0 ≤ positiveKernelPreparationBinLog p e := by
  have := positiveKernelPreparationParameter_nonneg hp
  unfold positiveKernelPreparationBinLog
  positivity

noncomputable def positiveKernelResidualPrecisionParameter (p : ℝ) (e : ℕ) : ℝ :=
  positiveKernelPreparationParameter p + positiveKernelPreparationParameter p +
    positiveKernelPreparationBinLog p e + 4

noncomputable def positiveKernelMarkovPrecisionParameter (p : ℝ) (e : ℕ) : ℝ :=
  (positiveKernelPreparationParameter p + positiveKernelPreparationBinLog p e) +
    (2 * positiveKernelPreparationParameter p + positiveKernelPreparationBinLog p e + 4) +
    (p + positiveKernelPreparationParameter p) + 2

theorem exists_positiveKernelPreparationParameters_bound (e : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      p + 3 ≤ (p + C) ^ C ∧
      positiveKernelPreparationParameter p ≤ (p + C) ^ C ∧
      positiveKernelPreparationBinLog p e ≤ (p + C) ^ C ∧
      positiveKernelResidualPrecisionParameter p e ≤ (p + C) ^ C ∧
      positiveKernelMarkovPrecisionParameter p e ≤ (p + C) ^ C := by
  let q : Polynomial ℕ := (Polynomial.X + 5) ^ positiveKernelPreparationExponent
  let bin : Polynomial ℕ := (2 * Polynomial.X + q + 5 + Polynomial.C e) ^ e
  let residual : Polynomial ℕ := q + q + bin + 4
  let markov : Polynomial ℕ := (q + bin) + (2 * q + bin + 4) + (Polynomial.X + q) + 2
  let total : Polynomial ℕ := Polynomial.X + 3 + q + bin + residual + markov
  obtain ⟨C, hC, hbound⟩ := Erdos3.exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hq := positiveKernelPreparationParameter_nonneg hp
  have hbin := positiveKernelPreparationBinLog_nonneg hp e
  have hresidual : 0 ≤ positiveKernelResidualPrecisionParameter p e := by
    unfold positiveKernelResidualPrecisionParameter
    positivity
  have hmarkov : 0 ≤ positiveKernelMarkovPrecisionParameter p e := by
    unfold positiveKernelMarkovPrecisionParameter
    positivity
  have htotal : p + 3 + positiveKernelPreparationParameter p +
      positiveKernelPreparationBinLog p e + positiveKernelResidualPrecisionParameter p e +
      positiveKernelMarkovPrecisionParameter p e ≤ (p + C) ^ C := by
    simpa [total, markov, residual, bin, q, positiveKernelPreparationParameter,
      positiveKernelPreparationBinLog, positiveKernelResidualPrecisionParameter,
      positiveKernelMarkovPrecisionParameter, Polynomial.eval₂_pow] using hbound p hp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

noncomputable def positiveKernelPreparationBudgetExponent (e : ℕ) : ℕ :=
  Classical.choose (exists_positiveKernelPreparationParameters_bound e)

theorem positiveKernelPreparationBudgetExponent_ge_two (e : ℕ) :
    2 ≤ positiveKernelPreparationBudgetExponent e :=
  (Classical.choose_spec (exists_positiveKernelPreparationParameters_bound e)).1

theorem positiveKernelPreparationBudget_bounds (e : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p + 3 ≤ (p + positiveKernelPreparationBudgetExponent e) ^ positiveKernelPreparationBudgetExponent e ∧
      positiveKernelPreparationParameter p ≤
        (p + positiveKernelPreparationBudgetExponent e) ^ positiveKernelPreparationBudgetExponent e ∧
      positiveKernelPreparationBinLog p e ≤
        (p + positiveKernelPreparationBudgetExponent e) ^ positiveKernelPreparationBudgetExponent e ∧
      positiveKernelResidualPrecisionParameter p e ≤
        (p + positiveKernelPreparationBudgetExponent e) ^ positiveKernelPreparationBudgetExponent e ∧
      positiveKernelMarkovPrecisionParameter p e ≤
        (p + positiveKernelPreparationBudgetExponent e) ^ positiveKernelPreparationBudgetExponent e :=
  (Classical.choose_spec (exists_positiveKernelPreparationParameters_bound e)).2 p hp

end Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}

namespace PositiveKernelPreparation

variable {p : ℝ} {e : ℕ} (prep : P.PositiveKernelPreparation p e)

theorem conclusion_of_selected
    {q : ℝ} (hq : 0 ≤ q)
    (out : prep.selected.problem.Conclusion q (Real.exp (-q)) (Real.exp (-q)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp q)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤
      Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) :
    Nonempty (P.Conclusion (3 * q + 2) (Real.exp (-(3 * q + 2)))
      (Real.exp (-(3 * q + 2)))) := by
  let top := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
  let K := frequencyCodeKernel top prep.early.eta prep.selected.code
  have hK : K ≤ D.filtration.layer s :=
    (finiteFrequencyKernel_le top _ _).trans inf_le_left
  have hkernel : K ≤ LinearMap.ker φ.toLinearMap :=
    (finiteFrequencyKernel_le top _ _).trans inf_le_right
  have hobservable : (fun x => (prep.selected.tests x).observable) =
      (fun x => ((prep.tests x).kernelProjection K hK).observable) := by
    funext x
    exact congrArg (fun T => T.observable) (prep.selected.identity x)
  have hscore : ∀ z : prep.selected.retained,
      Real.exp (-positiveKernelPreparationParameter p) ≤
        (P.candidate ⟨z.val, prep.selected.subset z.property⟩).score
          (fun x => ((prep.tests x).kernelProjection K hK).observable) weight := by
    intro z
    rw [← P.precenterCandidate_score_mem_eq prep.positive_mass z.val
      (prep.selected.subset z.property)]
    simpa only [prep.selected.identity] using prep.selected.scores z.val z.property
  have transport (newObservable : (X → ℤ) → D.Space → ℂ)
      (heq : (fun x => (prep.selected.tests x).observable) = newObservable)
      (hnewScore : ∀ z : prep.selected.retained,
        Real.exp (-positiveKernelPreparationParameter p) ≤
          (P.candidate ⟨z.val, prep.selected.subset z.property⟩).score newObservable weight) :
      Nonempty ((P.restrictObservable newObservable prep.selected.retained
        prep.selected.subset prep.selected.mass hnewScore).Conclusion q
          (Real.exp (-q)) (Real.exp (-q))) := by
    subst newObservable
    exact ⟨out⟩
  obtain ⟨projectedOut⟩ := transport _ hobservable hscore
  exact P.conclusion_of_kernel_projection_normalized prep.tests prep.tests_unit
    prep.tests_observable K hK hkernel prep.selected.retained prep.selected.subset
    prep.selected.mass hscore hq projectedOut hweight hσone Cgeo hCgeo hchart hsmall hpoly

end PositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure CommonKeepPositiveKernelPreparation (p : ℝ) (e : ℕ) where
  keep : LayerSamplerVariables G I n B → Prop
  refinement : P.Refinement cost (massThreshold * Real.exp (-p)) scoreThreshold
  hkeep : ∀ z : refinement.problem.productive, (refinement.problem.chart z).keep = keep
  prep : (refinement.problem.withKeep keep hkeep).PositiveKernelPreparation (2 * p) e

theorem exists_commonKeepPositiveKernelPreparation
    (p : ℝ) (e : ℕ) (hp : 0 ≤ p)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hD : D.GeometryComplexityLE p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hξ1 : ξ ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ η) :
    Nonempty (P.CommonKeepPositiveKernelPreparation p e) := by
  obtain ⟨keep, refinement, hkeep⟩ := P.exists_common_keep_refinement_exp
    ((Real.exp_pos _).le.trans hmass) hvariables
  have hp2 : p ≤ 2 * p := by linarith
  have hmass2 : Real.exp (-(2 * p)) ≤ massThreshold * Real.exp (-p) := by
    calc
      Real.exp (-(2 * p)) = Real.exp (-p) * Real.exp (-p) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ massThreshold * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
  have hnet2 : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((2 * p + Real.log (1 / η) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨count, hcount, centers, hcenters⟩ := hnet η hη hη1
    refine ⟨count, hcount.trans (Real.exp_le_exp.mpr ?_), centers, hcenters⟩
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hη1)
    exact pow_le_pow_left₀ (by positivity) (by linarith) e
  obtain ⟨prep⟩ := (refinement.problem.withKeep keep hkeep).exists_positiveKernelPreparation
    (2 * p) e (by positivity) (hD.mono D hp2) ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hp2)) hLip hpositive
    (fun x => (hweight x).trans (Real.exp_le_exp.mpr hp2)) hmass2
    ((Real.exp_le_exp.mpr (neg_le_neg hp2)).trans hscore) hξ1 hnet2
  exact ⟨{ keep := keep, refinement := refinement, hkeep := hkeep, prep := prep }⟩

namespace CommonKeepPositiveKernelPreparation

variable {P} {p : ℝ} {e : ℕ} (front : P.CommonKeepPositiveKernelPreparation p e)

noncomputable def problem := front.refinement.problem.withKeep front.keep front.hkeep

@[simp] theorem problem_keep (z : front.problem.productive) :
    (front.problem.chart z).keep = front.keep := rfl

theorem conclusion_of_selected
    {q : ℝ} (hq : 0 ≤ q)
    (out : front.prep.selected.problem.Conclusion q (Real.exp (-q)) (Real.exp (-q)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp q)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤
      Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) :
    Nonempty (P.Conclusion (3 * q + 2) (Real.exp (-(3 * q + 2)))
      (Real.exp (-(3 * q + 2)))) := by
  obtain ⟨restored⟩ := front.prep.conclusion_of_selected hq out hweight
    hσone Cgeo hCgeo hchart hsmall hpoly
  exact ⟨front.refinement.conclusion
    (front.refinement.problem.conclusion_of_withKeep front.keep front.hkeep restored)⟩

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
