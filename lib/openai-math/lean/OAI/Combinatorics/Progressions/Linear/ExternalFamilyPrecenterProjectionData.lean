import OAI.Combinatorics.Progressions.Estimates.ExternalPhysicalMemberPivotMasks
import OAI.Combinatorics.Progressions.Fourier.FrequencyProjectionBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L σ G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def kernelProjection (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) : D.Niltest w := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  exact T.averageCircles
    (fun i => D.centralRationalCircle (b i).val (hK (b i).property))
    (List.finRange (finrank ℚ K))

theorem kernelProjection_orbit (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) :
    (T.kernelProjection K hK).orbit = T.orbit := rfl

theorem kernelProjection_congr (T : D.Niltest w) {K K' : Submodule ℚ L}
    (hK : K ≤ D.filtration.layer s) (hK' : K' ≤ D.filtration.layer s) (h : K = K') :
    T.kernelProjection K hK = T.kernelProjection K' hK' := by
  subst K'
  rfl

theorem kernelProjection_complexity (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.kernelProjection K hK).ComplexityLE p := hT

theorem kernelProjection_unitInterval (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (hT : T.UnitIntervalValued) :
    (T.kernelProjection K hK).UnitIntervalValued := by
  unfold kernelProjection
  exact T.averageCircles_unit_interval _ _ hT

theorem kernelProjection_observable_congr (T U : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (hTU : T.observable = U.observable) :
    (T.kernelProjection K hK).observable = (U.kernelProjection K hK).observable := by
  unfold kernelProjection averageCircles
  dsimp only
  rw [hTU]

theorem kernelProjection_invariant (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (z : D.RealGroup) (hz : z.coord ∈ K.baseChange ℝ) (x : D.Space) :
    (T.kernelProjection K hK).observable (z • x) = (T.kernelProjection K hK).observable x := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  apply D.invariant_of_kernel_circles K hK b _ _ z hz x
  intro i t y
  apply T.averageCircles_invariant
  · dsimp only
    intro j _ k _
    exact D.centralRationalCircle_commutes (b j).val (b k).val (hK (b j).property) (hK (b k).property)
  · simp

theorem kernelProjection_tested_error [Fintype G] (T : D.Niltest w)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    {J : Type*} [Fintype J] (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (law : FiniteProbabilityWeights G) (path : G → D.Space) (weight : G → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (js : List J)
    (hsignificant : ∀ j, tau < ‖law.complexMean (fun x => weight x * (U j).observable (path x))‖ → j ∈ js) :
    ‖law.complexMean (fun x => weight x * T.observable (path x)) -
      law.complexMean (fun x => weight x *
        (T.kernelProjection (finiteFrequencyKernel P eta js)
          ((finiteFrequencyKernel_le P eta js).trans hP)).observable (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let K := finiteFrequencyKernel P eta js
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P eta js).trans hP
  let b := Module.finBasis ℚ K
  let A := fun i => D.centralRationalCircle (b i).val (hK (b i).property)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ t x, (U j).observable ((A i).act t x) = character (n • t) * (U j).observable x) ∧
      (eta j (b i).val = 0 → n = 0) :=
    D.exists_centralRationalCircle_frequency (b i).val (hK (b i).property)
      (eta j) (U j).observable (hvertical j)
  choose n heigen hzero using hfreq
  apply iteratedCircleAverage_tested_weighted_error law A (List.finRange (finrank ℚ K))
    T.observable (fun j => (U j).observable) n path weight T.lipBound (fun j => (U j).lipBound)
    T.lipschitz (fun j => (U j).lipschitz) hB htau hweight happrox
    (fun j i _ => heigen j i)
  intro j hj
  apply le_of_not_gt
  intro hlarge
  apply hj
  intro i _
  apply hzero j i
  exact ((mem_finiteFrequencyKernel P eta js (b i).val).mp (b i).property).2 j
    (hsignificant j hlarge)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators

variable {L σ X G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_external_family_centralRationalCircle_frequency
    (v : L) (hv : v ∈ D.filtration.layer s)
    (eta : L →ₗ[ℚ] ℚ) (f : X → D.Space → ℂ)
    (hf : ∀ a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      f a (z • x) =
        character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * f a x) :
    let := D.metricSpace
    ∃ n : ℤ,
      (∀ a t x, f a ((D.centralRationalCircle v hv).act t x) =
        character (n • t) * f a x) ∧
      (eta v = 0 → n = 0) := by
  classical
  let := D.metricSpace
  by_cases hz : ∀ a x, f a x = 0
  · exact ⟨0, fun a t x => by simp [hz], fun _ => rfl⟩
  push Not at hz
  obtain ⟨a, x, hax⟩ := hz
  obtain ⟨n, hn⟩ := vertical_frequency_integral_on_lattice D.filtration D.realLattice
    eta (f a) (hf a) ⟨x, hax⟩ (⟨D.periodicRealDirection v⟩ : D.RealGroup)
    (D.periodicRealDirection_mem_top v hv) (D.periodicRealDirection_mem_lattice v)
  refine ⟨n, ?_, ?_⟩
  · intro a t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [D.centralRationalCircle_act_coe]
    have hr : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r ∈ D.filtration.realification.subgroup s := by
      change r • D.periodicRealDirection v ∈ D.filtration.realLayer s
      exact (D.filtration.realLayer s).smul_mem r (D.periodicRealDirection_mem_top v hv)
    rw [hf a _ hr]
    apply congrArg (fun z : CircleFourier.Circle => character z * f a x)
    change ((realifyFunctional eta (r • D.periodicRealDirection v) : ℝ) : CircleFourier.Circle) =
      n • (r : CircleFourier.Circle)
    rw [map_smul, hn, ← AddCircle.coe_zsmul]
    congr 1
    simp only [smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro heta
    have hzero : realifyFunctional eta (D.periodicRealDirection v) = 0 := by
      simp [periodicRealDirection, realifyFunctional_tmul, heta]
    have hn0 : (n : ℝ) = 0 := hn.symm.trans hzero
    exact_mod_cast hn0

namespace Niltest

theorem external_family_kernelProjection_tested_error [Fintype G]
    (T : X → D.Niltest w) (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    {J : Type*} [Fintype J] (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
    (hvertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j a).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
          (U j a).observable x)
    (law : FiniteProbabilityWeights G) (physical : G → X)
    (path : G → D.Space) (weight : G → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ rho)
    (js : List J)
    (hsignificant : ∀ j,
      tau < ‖law.complexMean (fun x => weight x * (U j (physical x)).observable (path x))‖ →
        j ∈ js) :
    ‖law.complexMean (fun x => weight x * (T (physical x)).observable (path x)) -
      law.complexMean (fun x => weight x *
        ((T (physical x)).kernelProjection (finiteFrequencyKernel P eta js)
          ((finiteFrequencyKernel_le P eta js).trans hP)).observable (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let K := finiteFrequencyKernel P eta js
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P eta js).trans hP
  let b := Module.finBasis ℚ K
  let A := fun i => D.centralRationalCircle (b i).val (hK (b i).property)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ a t x, (U j a).observable ((A i).act t x) =
        character (n • t) * (U j a).observable x) ∧
      (eta j (b i).val = 0 → n = 0) :=
    exists_external_family_centralRationalCircle_frequency (b i).val (hK (b i).property)
      (eta j) (fun a => (U j a).observable) (hvertical j)
  choose n heigen hzero using hfreq
  apply iteratedCircleAverage_family_tested_weighted_error law A
    (List.finRange (finrank ℚ K)) (fun a => (T a).observable)
    (fun j a => (U j a).observable) n physical path weight
    (fun a => (T a).lipBound) (fun j a => (U j a).lipBound)
    (fun a => (T a).lipschitz) (fun j a => (U j a).lipschitz)
    hB htau hweight happrox (fun j i _ t a x => heigen j i a t x)
  intro j hj
  apply le_of_not_gt
  intro hlarge
  apply hj
  intro i _
  apply hzero j i
  exact ((mem_finiteFrequencyKernel P eta js (b i).val).mp (b i).property).2 j
    (hsignificant j hlarge)

end Niltest

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem kernelProjection_observable_sub_norm_le (T : D.Niltest w) (U : D.Niltest v)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) {ε : ℝ}
    (hTU : ∀ x, ‖T.observable x - U.observable x‖ ≤ ε) :
    ∀ x, ‖(T.kernelProjection K hK).observable x - (U.kernelProjection K hK).observable x‖ ≤ ε := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  exact iteratedCircleAverage_sub_norm_le
    (fun i => D.centralRationalCircle (b i).val (hK (b i).property))
    (List.finRange (finrank ℚ K)) T.lipschitz U.lipschitz hTU

theorem kernelProjection_normBound (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) :
    (T.kernelProjection K hK).normBound = T.normBound := rfl

theorem kernelProjection_lipBound (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) :
    (T.kernelProjection K hK).lipBound = T.lipBound := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier MeasureTheory
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_iteratedCentralCircle_translation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (v : ι → K) (is : List ι)
    (t : CircleAverageTuple is) :
    let := D.metricSpace
    ∃ g : D.RealGroup, g.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅g.coord, y⁆ = 0) ∧
      ∀ x, iteratedCircleAction
        (fun i => D.centralRationalCircle (v i) (hK (v i).property)) is t x = g • x := by
  let := D.metricSpace
  induction is with
  | nil =>
    refine ⟨1, (K.baseChange ℝ).zero_mem, fun y => zero_lie y, ?_⟩
    intro x
    exact (one_smul D.RealGroup x).symm
  | cons i is ih =>
    obtain ⟨g, hg, hcentral, hact⟩ := ih t.2
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective t.1
    let z : D.RealGroup := realBCHLine (D.periodicRealDirection (v i)) r
    have hz : z.coord ∈ K.baseChange ℝ := by
      apply (K.baseChange ℝ).smul_mem r
      change (1 : ℝ) ⊗ₜ[ℚ] ((D.rationalDirectionPeriod (v i) : ℚ) • (v i : L)) ∈ _
      exact Submodule.tmul_mem_baseChange_of_mem 1 (K.smul_mem _ (v i).property)
    have hzc : ∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0 := by
      intro y
      change ⁅r • D.periodicRealDirection (v i), y⁆ = 0
      rw [smul_lie, D.periodicRealDirection_central (v i) (hK (v i).property), smul_zero]
    have hcoord : (g * z).coord = g.coord + z.coord :=
      lieBCH_eq_add_of_lie_eq_zero D.filtration.realification.lowerCentralSeries_eq_bot
        (hcentral z.coord)
    refine ⟨g * z, ?_, ?_, ?_⟩
    · rw [hcoord]
      exact (K.baseChange ℝ).add_mem hg hz
    · intro y
      rw [hcoord, add_lie, hcentral, hzc, add_zero]
    · intro x
      change iteratedCircleAction _ is t.2
        ((D.centralRationalCircle (v i) (hK (v i).property)).act t.1 x) = _
      rw [hact, ← hr, D.centralRationalCircle_act_coe, mul_smul]

abbrev KernelProjectionParameters (K : Submodule ℚ L) :=
  CircleAverageTuple (List.finRange (finrank ℚ K))

noncomputable def kernelProjectionCircleFamily (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) :
    let := D.metricSpace
    Fin (finrank ℚ K) → IsometricCircleAction D.Space := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact fun i => D.centralRationalCircle (Module.finBasis ℚ K i)
    (hK (Module.finBasis ℚ K i).property)

theorem exists_kernelProjectionTranslation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) :
    let := D.metricSpace
    ∃ g : D.RealGroup, g.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅g.coord, y⁆ = 0) ∧
      ∀ x, iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
        (List.finRange (finrank ℚ K)) t x = g • x := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact D.exists_iteratedCentralCircle_translation K hK (Module.finBasis ℚ K)
    (List.finRange (finrank ℚ K)) t

noncomputable def kernelProjectionTranslation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) : D.RealGroup :=
  (D.exists_kernelProjectionTranslation K hK t).choose

theorem kernelProjectionTranslation_mem (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) :
    (D.kernelProjectionTranslation K hK t).coord ∈ K.baseChange ℝ :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.1

theorem kernelProjectionTranslation_central (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K)
    (y : ℝ ⊗[ℚ] L) : ⁅(D.kernelProjectionTranslation K hK t).coord, y⁆ = 0 :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.2.1 y

theorem kernelProjectionTranslation_act (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) (x : D.Space) :
    let := D.metricSpace
    iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
      (List.finRange (finrank ℚ K)) t x = D.kernelProjectionTranslation K hK t • x :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.2.2 x

theorem continuous_kernelProjectionTranslation_act (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    let := D.metricSpace
    Continuous (fun t => D.kernelProjectionTranslation K hK t • x) := by
  let := D.metricSpace
  have he : (fun t => D.kernelProjectionTranslation K hK t • x) =
      (fun t => iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
        (List.finRange (finrank ℚ K)) t x) :=
    funext (fun t => (D.kernelProjectionTranslation_act K hK t x).symm)
  rw [he]
  exact continuous_iteratedCircleAction_parameter _ _ _

namespace Niltest

variable {D} {σ : Type*} {w : σ → ℕ}

theorem continuous_kernelProjectionTranslation_observable (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    Continuous (fun t => T.observable (D.kernelProjectionTranslation K hK t • x)) := by
  let := D.metricSpace
  exact T.lipschitz.continuous.comp (D.continuous_kernelProjectionTranslation_act K hK x)

theorem integrable_kernelProjectionTranslation_observable (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    Integrable (fun t => T.observable (D.kernelProjectionTranslation K hK t • x))
      (circleAverageTupleMeasure (List.finRange (finrank ℚ K))) :=
  (T.continuous_kernelProjectionTranslation_observable K hK x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem kernelProjection_observable_eq_integral (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    (T.kernelProjection K hK).observable x =
      ∫ t, T.observable (D.kernelProjectionTranslation K hK t • x)
        ∂circleAverageTupleMeasure (List.finRange (finrank ℚ K)) := by
  let := D.metricSpace
  change iteratedCircleAverage (D.kernelProjectionCircleFamily K hK)
    (List.finRange (finrank ℚ K)) T.observable x = _
  rw [iteratedCircleAverage_eq_integral _ _ T.lipschitz.continuous]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => congrArg T.observable
    (D.kernelProjectionTranslation_act K hK t x))

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_common_positive_kernel_projection
    {L σ Ω G J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype G] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : D.Niltest w) (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights G) (path : Ω → G → D.Space) (weight : Ω → G → ℂ)
    {B rho tau delta : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ a x, ‖weight a x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hscore : ∀ a ∈ productive,
      delta ≤ ((localLaw a).complexMean (fun x => weight a x * T.observable (path a x))).re)
    (hsmall : 2 * B * rho + Fintype.card J * tau ≤ delta / 2) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (S : D.Niltest w) (retained : Finset Ω),
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j →
          tau < ‖(localLaw a).complexMean (fun x => weight a x * (U j).observable (path a x))‖) ∧
        delta / 2 ≤ ((localLaw a).complexMean (fun x => weight a x * S.observable (path a x))).re := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let js : Ω → List J := fun a => (Finset.univ.filter (fun j =>
    tau < ‖(localLaw a).complexMean (fun x => weight a x * (U j).observable (path a x))‖)).toList
  obtain ⟨code, retained, hretained, hmass, hcode⟩ :=
    exists_common_frequency_kernel outer productive P eta js
  let K := frequencyCodeKernel P eta code
  have hK : K ≤ D.filtration.layer s :=
    (finiteFrequencyKernel_le P _ _).trans hP
  let S := T.kernelProjection K hK
  refine ⟨code, S, retained, T.kernelProjection_unitInterval K hK hT,
    T.kernelProjection_complexity K hK hTc, T.kernelProjection_orbit K hK,
    ?_, hretained, hmass, ?_⟩
  · intro z hz x
    exact T.kernelProjection_invariant K hK z hz x
  · intro a ha
    obtain ⟨hpivots, hk⟩ := hcode a ha
    have hsignificant (j : J)
        (hj : tau < ‖(localLaw a).complexMean (fun x => weight a x * (U j).observable (path a x))‖) :
        j ∈ js a := by simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have herr := T.kernelProjection_tested_error P hP eta U hvertical (localLaw a)
      (path a) (weight a) hB htau (hweight a) happrox (js a) hsignificant
    rw [T.kernelProjection_congr _ hK hk] at herr
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hpivots i j hij
    · have hr := Complex.re_le_norm
        ((localLaw a).complexMean (fun x => weight a x * T.observable (path a x)) -
          (localLaw a).complexMean (fun x => weight a x * S.observable (path a x)))
      rw [Complex.sub_re] at hr
      have hs := hscore a (hretained ha)
      change ‖(localLaw a).complexMean (fun x => weight a x * T.observable (path a x)) -
        (localLaw a).complexMean (fun x => weight a x * S.observable (path a x))‖ ≤ _ at herr
      linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_common_positive_kernel_projection
    {L σ X Ω G J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype G] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    {p : ℝ} (hTc : ∀ x, (T x).ComplexityLE p)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
    (hvertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j a).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
          (U j a).observable x)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
    (path : Ω → G → D.Space) (weight : Ω → G → ℂ)
    {B rho tau delta : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ a x, ‖weight a x‖ ≤ B)
    (happrox : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ rho)
    (hscore : ∀ a ∈ productive,
      delta ≤ ((localLaw a).complexMean (fun x =>
        weight a x * (T (physical a x)).observable (path a x))).re)
    (hsmall : 2 * B * rho + Fintype.card J * tau ≤ delta / 2) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w)
      (retained : Finset Ω),
      (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
        ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE p ∧ (S x).orbit = (T x).orbit) ∧
      (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j →
          tau < ‖(localLaw a).complexMean (fun x =>
            weight a x * (U j (physical a x)).observable (path a x))‖) ∧
        delta / 2 ≤ ((localLaw a).complexMean (fun x =>
          weight a x * (S (physical a x)).observable (path a x))).re := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let js : Ω → List J := fun a => (Finset.univ.filter (fun j =>
    tau < ‖(localLaw a).complexMean (fun x =>
      weight a x * (U j (physical a x)).observable (path a x))‖)).toList
  obtain ⟨code, retained, hretained, hmass, hcode⟩ :=
    exists_common_frequency_kernel outer productive P eta js
  let K := frequencyCodeKernel P eta code
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
  let S := fun x => (T x).kernelProjection K hK
  refine ⟨code, S, retained, fun _ => rfl, ?_, ?_, hretained, hmass, ?_⟩
  · intro x
    exact ⟨(T x).kernelProjection_unitInterval K hK (hT x),
      (T x).kernelProjection_complexity K hK (hTc x), (T x).kernelProjection_orbit K hK⟩
  · intro a z hz x
    exact (T a).kernelProjection_invariant K hK z hz x
  · intro a ha
    obtain ⟨hpivots, hk⟩ := hcode a ha
    have hsignificant (j : J)
        (hj : tau < ‖(localLaw a).complexMean (fun x =>
          weight a x * (U j (physical a x)).observable (path a x))‖) : j ∈ js a := by
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have herr := external_family_kernelProjection_tested_error T P hP eta U hvertical
      (localLaw a) (physical a) (path a) (weight a) hB htau (hweight a) happrox
      (js a) hsignificant
    have hproj (x : X) : (T x).kernelProjection (finiteFrequencyKernel P eta (js a))
        ((finiteFrequencyKernel_le P eta (js a)).trans hP) = S x :=
      (T x).kernelProjection_congr _ hK hk
    simp_rw [hproj] at herr
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        using hpivots i j hij
    · have hr := Complex.re_le_norm
        ((localLaw a).complexMean (fun x => weight a x * (T (physical a x)).observable (path a x)) -
          (localLaw a).complexMean (fun x => weight a x * (S (physical a x)).observable (path a x)))
      rw [Complex.sub_re] at hr
      have hs := hscore a (hretained ha)
      linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_contractive_quantitative_kernel_projection_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype G]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
        (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
          (U j x).lipBound = (T x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j a).observable x) ∧
        (∀ j a b (ε : ℝ),
          (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
          ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
        (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE ((p + 2) ^ C) ∧
          (S x).orbit = (T x).orbit) ∧
        (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
          ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
        (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun x =>
              weight a x * (U j (physical a x)).observable (path a x))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
            (fun x => weight a x * (S (physical a x)).observable (path a x))).re := by
  let R : Polynomial ℕ := Polynomial.X
  let Q := 2 * R + 8
  let A := (Q + 3) ^ 9 + 2 * Q + 2
  let V := 2 * A * (2 * A + 2) ^ 4 + ((2 * A + 2) ^ 4 + A + (Q + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + 2 * V + R + 10 + R * (V + 1))
  refine ⟨C, hC, ?_⟩
  intro L σ X Ω G _ _ s d _ _ _ _ _ _ D w T p hp hD hT hTc P hP
    outer productive localLaw physical path weight hweight hscore
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let q := 2 * p + 8
  let v := verticalDecompositionBudget q
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg hq
  have hprod : 0 ≤ p * (v + 1) := by positivity
  have hb : q + 2 * v + p + 10 + p * (v + 1) ≤ (p + 2) ^ C := by
    simpa [R, Q, A, V, q, v, verticalDecompositionBudget, centralActionBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hvC : v ≤ (p + 2) ^ C := by linarith
  have htC : p + v + 8 ≤ (p + 2) ^ C := by linarith
  have hnC : p * (v + 1) ≤ (p + 2) ^ C := by linarith
  have hsC : p + 1 ≤ (p + 2) ^ C := by linarith
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hint, hchar, hcontract, happrox, hintError, hrealError⟩ :=
    D.exists_externalFamily_contractive_vertical_expansion hq (hD.mono D hpq) T
      (fun x => (hTc x).mono hpq) (Real.exp (-q)) (Real.exp_pos (-q))
      (by rw [Real.exp_neg, inv_inv])
  let _ := inst
  have hsmall := frequency_projection_error_bound hp hJ
  obtain ⟨code, S, retained, hidentity, hS, hSinv, hretained, hmass, hlocal⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_family_common_positive_kernel_projection
      T hT hTc P hP eta U hvert outer productive localLaw physical path weight
      (Real.exp_nonneg p) (Real.exp_nonneg (-(p + v + 8))) hweight happrox hscore hsmall
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have h := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  refine ⟨J, inst, eta, U, code, S, retained,
    hJ.trans (Real.exp_le_exp.mpr hvC), fun j i => (hheight j i).trans hvC,
    fun j x => ⟨(hU j x).1.mono hqC, (hU j x).2⟩, hvert, hcontract,
    fun x => ⟨(hS x).1, (hS x).2.1.mono (hpq.trans hqC), (hS x).2.2⟩,
    hidentity, hSinv, hretained, ?_, ?_⟩
  · exact (mass_div_frequency_count (outer.mass_nonneg productive) hp hv hdim hJ hnC).trans hmass
  · intro a ha
    obtain ⟨hpivot, hpositive⟩ := hlocal a ha
    refine ⟨fun i j hij => (Real.exp_le_exp.mpr (neg_le_neg htC)).trans_lt (hpivot i j hij), ?_⟩
    exact ((Real.exp_le_exp.mpr (by linarith : -((p + 2) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))).trans hpositive

end Erdos3

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_precenter_kernel_projection_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
          (U j x).lipBound = (T x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j a).observable x) ∧
        (∀ j a b (ε : ℝ),
          (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
          ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
      ∀ {Ω G : Type*} [Fintype Ω] [Fintype G],
      ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
        (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
      ∃ (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w)
        (retained : Finset Ω),
        (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE ((p + 2) ^ C) ∧
          (S x).orbit = (T x).orbit) ∧
        (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
          ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
        (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun x =>
              weight a x * (U j (physical a x)).observable (path a x))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
            (fun x => weight a x * (S (physical a x)).observable (path a x))).re := by
  let R : Polynomial ℕ := Polynomial.X
  let Q := 2 * R + 8
  let A := (Q + 3) ^ 9 + 2 * Q + 2
  let V := 2 * A * (2 * A + 2) ^ 4 + ((2 * A + 2) ^ 4 + A + (Q + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + 2 * V + R + 10 + R * (V + 1))
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ s d _ _ _ _ D w T p hp hD hT hTc
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let q := 2 * p + 8
  let v := verticalDecompositionBudget q
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg hq
  have hprod : 0 ≤ p * (v + 1) := by positivity
  have hb : q + 2 * v + p + 10 + p * (v + 1) ≤ (p + 2) ^ C := by
    simpa [R, Q, A, V, q, v, verticalDecompositionBudget, centralActionBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hvC : v ≤ (p + 2) ^ C := by linarith
  have htC : p + v + 8 ≤ (p + 2) ^ C := by linarith
  have hnC : p * (v + 1) ≤ (p + 2) ^ C := by linarith
  have hsC : p + 1 ≤ (p + 2) ^ C := by linarith
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hint, hchar, hcontract, happrox, hintError, hrealError⟩ :=
    D.exists_externalFamily_contractive_vertical_expansion hq (hD.mono D hpq) T
      (fun x => (hTc x).mono hpq) (Real.exp (-q)) (Real.exp_pos (-q))
      (by rw [Real.exp_neg, inv_inv])
  let _ := inst
  refine ⟨J, inst, eta, U,
    hJ.trans (Real.exp_le_exp.mpr hvC), fun j i => (hheight j i).trans hvC,
    fun j x => ⟨(hU j x).1.mono hqC, (hU j x).2⟩, hvert, hcontract, ?_⟩
  intro Ω G _ _ P hP outer productive localLaw physical path weight hweight hscore
  have hsmall := frequency_projection_error_bound hp hJ
  obtain ⟨code, S, retained, hidentity, hS, hSinv, hretained, hmass, hlocal⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_family_common_positive_kernel_projection
      T hT hTc P hP eta U hvert outer productive localLaw physical path weight
      (Real.exp_nonneg p) (Real.exp_nonneg (-(p + v + 8))) hweight happrox hscore hsmall
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have h := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  refine ⟨code, S, retained,
    fun x => ⟨(hS x).1, (hS x).2.1.mono (hpq.trans hqC), (hS x).2.2⟩,
    hidentity, hSinv, hretained, ?_, ?_⟩
  · exact (mass_div_frequency_count (outer.mass_nonneg productive) hp hv hdim hJ hnC).trans hmass
  · intro a ha
    obtain ⟨hpivot, hpositive⟩ := hlocal a ha
    refine ⟨fun i j hij => (Real.exp_le_exp.mpr (neg_le_neg htC)).trans_lt (hpivot i j hij), ?_⟩
    exact ((Real.exp_le_exp.mpr (by linarith : -((p + 2) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))).trans hpositive

end Erdos3

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

structure ExternalFamilyPrecenterProjectionData
    {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : X → D.Niltest w) (p q : ℝ) where
  Freq : Type
  instFintype : Fintype Freq
  eta : Freq → L →ₗ[ℚ] ℚ
  U : Freq → X → D.Niltest w
  card_bound : (@Fintype.card Freq instFintype : ℝ) ≤ Real.exp q
  eta_height : ∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ q
  U_bounds : ∀ j x, (U j x).ComplexityLE q ∧
    (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
    (U j x).lipBound = (T x).lipBound
  vertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
    (U j a).observable (z • x) =
      character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
        (U j a).observable x
  contractive : ∀ j a b (ε : ℝ),
    (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
    ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε
  select : ∀ {Ω G : Type} [Fintype Ω] [Fintype G],
    ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
    ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
      (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
      (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
    (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
    (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
      (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
    ∃ (code : Fin (finrank ℚ P) → Option Freq) (S : X → D.Niltest w)
      (retained : Finset Ω),
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE q ∧
        (S x).orbit = (T x).orbit) ∧
      (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
        ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
      (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive * Real.exp (-q) ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j → Real.exp (-q) <
          ‖(localLaw a).complexMean (fun x =>
            weight a x * (U j (physical a x)).observable (path a x))‖) ∧
        Real.exp (-q) ≤ ((localLaw a).complexMean
          (fun x => weight a x * (S (physical a x)).observable (path a x))).re

attribute [instance] ExternalFamilyPrecenterProjectionData.instFintype

theorem exists_externalFamilyPrecenterProjectionData :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      Nonempty (ExternalFamilyPrecenterProjectionData T p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hproduce⟩ := exists_external_family_precenter_kernel_projection_budget
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ s d _ _ _ _ D w T p hp hD hT hTc
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hcontract, hselect⟩ :=
    hproduce T p hp hD hT hTc
  exact ⟨{
    Freq := J
    instFintype := inst
    eta := eta
    U := U
    card_bound := hJ
    eta_height := hheight
    U_bounds := hU
    vertical := hvert
    contractive := hcontract
    select := hselect }⟩

end Erdos3

end

end OAI
