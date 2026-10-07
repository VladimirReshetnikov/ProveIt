import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import OAI.Combinatorics.Progressions.Fourier.WeightedTranslationTwistedCentralFrequency
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
import OAI.Combinatorics.Progressions.Lattices.ResidueStrideRebase

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem detector_of_unit_detector {X : Type*} [Fintype X]
    (μ : FiniteProbabilityWeights X) (S : Seminorm ℂ (X → ℂ)) (atoms : Set (X → ℂ))
    {R δ β : ℝ} (hR : 0 < R)
    (hdetect : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) → δ / R ≤ S g →
      ∃ Q ∈ atoms, β ≤ ‖μ.correlation g Q‖)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ R) (hS : δ ≤ S f) :
    ∃ Q ∈ atoms, R * β ≤ ‖μ.correlation f Q‖ := by
  let g : X → ℂ := (R : ℂ)⁻¹ • f
  have hg (x : X) : ‖g x‖ ≤ 1 := by
    change ‖(R : ℂ)⁻¹ * f x‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    calc
      R⁻¹ * ‖f x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hf x) (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hSg : δ / R ≤ S g := by
    dsimp only [g]
    rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hR.le)
  obtain ⟨Q, hQ, hcorr⟩ := hdetect g hg hSg
  have heq : μ.correlation g Q = (R : ℂ)⁻¹ * μ.correlation f Q := by
    simp only [FiniteProbabilityWeights.correlation, g, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le] at hcorr
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcorr hR.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] using h

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleCorrelation {σ X : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x * star (test.eval (sample x))‖

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeSampleCorrelation

variable {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {S : Finset X} {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def mono (V : NativeSampleCorrelation w s p S sample f) (hpq : p ≤ q) :
    NativeSampleCorrelation w s q S sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

theorem exists_of_expansion {eta : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p eta) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 x ∈ S, f x * star (eta (sample x))‖) :
    Nonempty (NativeSampleCorrelation w s (q + p) S sample f) := by
  obtain ⟨i, hi⟩ := E.select_sample_correlation S sample f hcorr
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := hi }⟩

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

structure NativeSampleModel {σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def NativeSampleModel.constOne (hp : 2 ≤ p) :
    NativeSampleModel w degree p sample (fun _ => 1) where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold degree
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold degree) w 1
  norm := by simp [RationalFilteredNilmanifold.Niltest.const]
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree w hp
  eval _ := rfl

noncomputable def NativeSampleCorrelation.ofMean {S : Finset X} (hp : 2 ≤ p)
    (hmean : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x‖) :
    NativeSampleCorrelation w degree p S sample f where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold degree
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold degree) w 1
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree w hp
  correlation := by simpa only [RationalFilteredNilmanifold.Niltest.eval_const, star_one, mul_one] using hmean

noncomputable def NativeSampleModel.smul (F : NativeSampleModel w degree p sample f)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : NativeSampleModel w degree p sample (c • f) where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test.scaleComplex c
  norm := (F.test.scaleComplex_norm hc).trans F.norm
  complexity := F.test.scaleComplex_complexity hc F.complexity
  eval x := by change c * f x = c * F.test.eval (sample x); rw [F.eval]

theorem NativeSampleModel.norm_le (F : NativeSampleModel w degree p sample f) (x : X) :
    ‖f x‖ ≤ 1 := by
  rw [F.eval]
  exact (F.test.norm_eval_le _).trans F.norm

noncomputable def NativeSampleCorrelation.toSampleModel {S : Finset X}
    (V : NativeSampleCorrelation w degree p S sample f) (hV : V.test.normBound ≤ 1) :
    NativeSampleModel w degree p sample (fun x => V.test.eval (sample x)) where
  L := V.L
  dim := V.dim
  model := V.model
  test := V.test
  norm := hV
  complexity := V.complexity
  eval _ := rfl

def twistedNativeSampleFunctions {I : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (twist : I → X → ℂ) : Set (X → ℂ) :=
  {f | f = 0 ∨ ∃ i g, Nonempty (NativeSampleModel w degree p sample g) ∧
    f = fun x => star (twist i x) * g x}

theorem twistedNativeSampleFunctions_zero {I : Type*} (twist : I → X → ℂ) :
    (0 : X → ℂ) ∈ twistedNativeSampleFunctions w degree p sample twist := Or.inl rfl

theorem twistedNativeSampleFunctions_balanced {I : Type*} (twist : I → X → ℂ) :
    Balanced ℂ (twistedNativeSampleFunctions w degree p sample twist) := by
  rintro c hc _ ⟨f, hf, rfl⟩
  rcases hf with rfl | ⟨i, g, ⟨G⟩, rfl⟩
  · exact Or.inl (smul_zero c)
  · refine Or.inr ⟨i, c • g, ⟨G.smul c hc⟩, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem twistedNativeSampleFunctions_norm {I : Type*} (twist : I → X → ℂ)
    (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    (hf : f ∈ twistedNativeSampleFunctions w degree p sample twist) (x : X) : ‖f x‖ ≤ 1 := by
  rcases hf with rfl | ⟨i, g, ⟨G⟩, rfl⟩
  · simp
  · rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (htwist i x)).trans (G.norm_le x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem nativeCorrelation_restrict_model {A σ : Type*}
    (S : Finset A) (hS : S.Nonempty)
    (w : σ → ℕ) (degree : ℕ) (p : ℝ) (sample : A → σ → ℤ)
    (f twist : A → ℂ)
    (V : NativeSampleCorrelation w degree p S sample
      (fun x => f x * twist x))
    (hV : V.test.normBound ≤ 1) :
    ∃ G : S → ℂ, Nonempty (NativeSampleModel w degree p (fun x => sample x.val) G) ∧
      Real.exp (-p) ≤ ‖(FiniteProbabilityWeights.uniformFinset S hS).correlation (fun x => f x.val)
        (fun x => star (twist x.val) * G x)‖ := by
  let G : S → ℂ := fun x => V.test.eval (sample x.val)
  refine ⟨G, ⟨?_⟩, ?_⟩
  · exact {
      L := V.L
      dim := V.dim
      model := V.model
      test := V.test
      norm := hV
      complexity := V.complexity
      eval := fun _ => rfl }
  have hc := V.correlation
  rw [← FiniteProbabilityWeights.uniformFinset_complexMean S hS
    (fun x => (f x * twist x) * star (V.test.eval (sample x)))] at hc
  simpa only [G, FiniteProbabilityWeights.correlation, FiniteProbabilityWeights.complexMean,
    star_mul, star_star, mul_assoc, mul_left_comm, mul_comm] using hc

theorem nativeCorrelation_finite_site_model {A σ : Type*}
    (S : Finset A) (hS : S.Nonempty) [Nonempty S]
    (w : σ → ℕ) (degree : ℕ) (p : ℝ) (sample : A → σ → ℤ)
    (g : S → ℂ) (twist : A → ℂ)
    (V : NativeSampleCorrelation w degree p S sample
      (fun x => finiteSiteExtension Subtype.val g x * twist x))
    (hV : V.test.normBound ≤ 1) :
    ∃ G : S → ℂ, Nonempty (NativeSampleModel w degree p (fun x => sample x.val) G) ∧
      Real.exp (-p) ≤ ‖(FiniteProbabilityWeights.uniformFinset S hS).correlation g
        (fun x => star (twist x.val) * G x)‖ := by
  obtain ⟨G, hG, hc⟩ := nativeCorrelation_restrict_model S hS w degree p sample
    (finiteSiteExtension Subtype.val g) twist V hV
  refine ⟨G, hG, ?_⟩
  simpa only [finiteSiteExtension_apply Subtype.val Subtype.val_injective] using hc

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem commonStridePoint_index_of_mem {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (len : I → ℕ) {y : I → ℤ}
    (hy : y ∈ commonStrideBox c m len) :
    commonStridePoint c m (commonStrideIndex c m y) = y := by
  rw [commonStrideBox_eq_image] at hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  change commonStridePoint c m (commonStrideIndex c m (commonStridePoint c m x)) =
    commonStridePoint c m x
  by_cases hm : m = 0
  · subst m
    funext i
    change c i + (0 : ℤ) * _ = c i + (0 : ℤ) * x i
    simp only [zero_mul, add_zero]
  · rw [commonStrideIndex_point c (Nat.pos_of_ne_zero hm)]

namespace RationalFilteredNilmanifold.Niltest

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {degree dim : ℕ}
  {D : RationalFilteredNilmanifold L degree dim}

noncomputable def commonStridePullback (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) : D.Niltest (fun _ : I => 1) :=
  T.affinePullback (residueStepMatrix (fun _ : I => m)) c

@[simp] theorem commonStridePullback_observable (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) :
    (T.commonStridePullback c m).observable = T.observable := rfl

@[simp] theorem commonStridePullback_normBound (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) :
    (T.commonStridePullback c m).normBound = T.normBound := rfl

@[simp] theorem commonStridePullback_lipBound (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) :
    (T.commonStridePullback c m).lipBound = T.lipBound := rfl

@[simp] theorem commonStridePullback_complexityLE (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) (p : ℝ) :
    (T.commonStridePullback c m).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem commonStridePullback_eval (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) (x : I → ℤ) :
    (T.commonStridePullback c m).eval x = T.eval (commonStridePoint c m x) := by
  rw [commonStridePullback, eval_affinePullback, integerAffineMap_residueStepMatrix]
  rfl

theorem commonStridePullback_eval_index_of_modEq (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) (y : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) :
    (T.commonStridePullback c m).eval (commonStrideIndex c m y) = T.eval y := by
  rw [commonStridePullback_eval, commonStridePoint_index_of_modEq c m y hy]

theorem commonStridePullback_eval_index_of_mem (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) (len : I → ℕ) (y : I → ℤ)
    (hy : y ∈ commonStrideBox c m len) :
    (T.commonStridePullback c m).eval (commonStrideIndex c m y) = T.eval y := by
  rw [commonStridePullback_eval, commonStridePoint_index_of_mem c m len hy]

end RationalFilteredNilmanifold.Niltest

namespace RationalFilteredNilmanifold.Niltest

variable {I Ω : Type*} {L : Type} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {degree dim : ℕ}
  {D : RationalFilteredNilmanifold L degree dim} {p : ℝ}

noncomputable def commonStrideSampleModelOfModEq (T : D.Niltest (fun _ : I => 1))
    (hnorm : T.normBound ≤ 1) (hcomplexity : T.ComplexityLE p)
    (c : I → ℤ) (m : ℕ) (site : Ω → I → ℤ)
    (hsite : ∀ x i, site x i ≡ c i [ZMOD (m : ℤ)]) :
    NativeSampleModel (fun _ : I => 1) degree p
      (fun x => commonStrideIndex c m (site x)) (fun x => T.eval (site x)) where
  L := L
  dim := dim
  model := D
  test := T.commonStridePullback c m
  norm := hnorm
  complexity := hcomplexity
  eval x := (T.commonStridePullback_eval_index_of_modEq c m (site x) (hsite x)).symm

noncomputable def commonStrideSampleModel (T : D.Niltest (fun _ : I => 1))
    (hnorm : T.normBound ≤ 1) (hcomplexity : T.ComplexityLE p)
    (c : I → ℤ) (m : ℕ) (len : I → ℕ) :
    NativeSampleModel (fun _ : I => 1) degree p
      (fun y : commonStrideBox c m len => commonStrideIndex c m y.val)
      (fun y => T.eval y.val) where
  L := L
  dim := dim
  model := D
  test := T.commonStridePullback c m
  norm := hnorm
  complexity := hcomplexity
  eval y := (T.commonStridePullback_eval_index_of_mem c m len y.val y.property).symm

noncomputable def residueSliceSampleModel (T : D.Niltest (fun _ : I => 1))
    (hnorm : T.normBound ≤ 1) (hcomplexity : T.ComplexityLE p)
    {N : I → ℕ} {m : ℕ} (slice : ResidueBoxSlice N m) :
    NativeSampleModel (fun _ : I => 1) degree p
      (fun y : slice.integerPoints =>
        commonStrideIndex (fun i => (slice.start i : ℤ)) m y.val)
      (fun y => T.eval y.val) where
  L := L
  dim := dim
  model := D
  test := T.commonStridePullback (fun i => (slice.start i : ℤ)) m
  norm := hnorm
  complexity := hcomplexity
  eval y := by
    apply (T.commonStridePullback_eval_index_of_mem
      (fun i => (slice.start i : ℤ)) m slice.length y.val _).symm
    rw [← slice.integerPoints_eq_commonStrideBox]
    exact y.property

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

structure VerticalExpansion (native : NativeSampleModel w degree p sample f)
    (q rho : ℝ) where
  I : Type
  [finite : Fintype I]
  frequency : I → native.L →ₗ[ℚ] ℚ
  component : I → native.model.Niltest w
  card_le : (Fintype.card I : ℝ) ≤ Real.exp (verticalDecompositionBudget q)
  height_le : ∀ i j, rationalLogHeight (frequency i (native.model.basis j)) ≤
    verticalDecompositionBudget q
  orbit_eq : ∀ i, (component i).orbit = native.test.orbit
  norm_eq : ∀ i, (component i).normBound = native.test.normBound
  lip_eq : ∀ i, (component i).lipBound = native.test.lipBound
  vertical : ∀ i (z : native.model.RealGroup),
    z ∈ native.model.filtration.realification.subgroup degree → ∀ x,
      (component i).observable (z • x) =
        character ((realifyFunctional (frequency i) z.coord : ℝ) : CircleFourier.Circle) *
          (component i).observable x
  integral : ∀ i, (∃ x, (component i).observable x ≠ 0) →
    ∀ z : native.model.RealGroup,
      z ∈ native.model.filtration.realification.subgroup degree →
      z ∈ native.model.realLattice → ∃ n : ℤ, realifyFunctional (frequency i) z.coord = n
  preserves_character : ∀ (z : native.model.RealGroup) (c : ℂ),
    (∀ x, native.test.observable (z • x) = c * native.test.observable x) →
      ∀ i x, (component i).observable (z • x) = c * (component i).observable x
  observable_error : ∀ x,
    ‖(∑ i, (component i).observable x) - native.test.observable x‖ ≤ rho

attribute [instance] VerticalExpansion.finite

theorem exists_verticalExpansion (native : NativeSampleModel w degree p sample f)
    {q rho : ℝ} (hq : 0 ≤ q) (hpq : p ≤ q) (hrho : 0 < rho)
    (hrhoq : rho⁻¹ ≤ Real.exp q) : Nonempty (native.VerticalExpansion q rho) := by
  obtain ⟨I, inst, frequency, component, hcard, hheight, hcert,
      hvert, hint, hpres, herr, _⟩ :=
    native.test.exists_vertical_decomposition_preserving_bounds_and_characters hq
      (native.complexity.mono hpq) hrho hrhoq
  exact ⟨{
    I := I
    finite := inst
    frequency := frequency
    component := component
    card_le := hcard
    height_le := hheight
    orbit_eq := fun i => (hcert i).2.1
    norm_eq := fun i => (hcert i).2.2.1
    lip_eq := fun i => (hcert i).2.2.2
    vertical := hvert
    integral := hint
    preserves_character := hpres
    observable_error := herr }⟩

theorem exists_verticalExpansion_exp_error (native : NativeSampleModel w degree p sample f)
    {r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    Nonempty (native.VerticalExpansion (p + r) (Real.exp (-r))) := by
  apply native.exists_verticalExpansion (add_nonneg hp hr) (le_add_of_nonneg_right hr)
    (Real.exp_pos _)
  rw [Real.exp_neg, inv_inv]
  exact Real.exp_le_exp.mpr (le_add_of_nonneg_left hp)

namespace VerticalExpansion

variable {native : NativeSampleModel w degree p sample f} {q rho : ℝ}
  (E : native.VerticalExpansion q rho)

theorem complexity (i : E.I) : (E.component i).ComplexityLE p := by
  refine ⟨native.complexity.1, ?_⟩
  rw [E.norm_eq, E.lip_eq]
  exact native.complexity.2

theorem normBound_le (i : E.I) : (E.component i).normBound ≤ 1 := by
  rw [E.norm_eq]
  exact native.norm

theorem eval_error (x : σ → ℤ) :
    ‖(∑ i, (E.component i).eval x) - native.test.eval x‖ ≤ rho := by
  simpa only [RationalFilteredNilmanifold.Niltest.eval, E.orbit_eq] using
    E.observable_error (QuotientGroup.mk
      (native.model.filtration.realification.polynomialOrbitEval w x native.test.orbit))

theorem evalReal_error (x : σ → ℝ) :
    ‖(∑ i, (E.component i).evalReal x) - native.test.evalReal x‖ ≤ rho := by
  simpa only [RationalFilteredNilmanifold.Niltest.evalReal, E.orbit_eq] using
    E.observable_error (QuotientGroup.mk
      (native.model.filtration.realification.polynomialOrbitRealEval w x native.test.orbit))

theorem sample_error (x : X) :
    ‖(∑ i, (E.component i).eval (sample x)) - f x‖ ≤ rho := by
  rw [native.eval]
  exact E.eval_error (sample x)

theorem norm_eval_le (i : E.I) (x : σ → ℤ) : ‖(E.component i).eval x‖ ≤ 1 :=
  ((E.component i).norm_eval_le x).trans (E.normBound_le i)

theorem norm_evalReal_le (i : E.I) (x : σ → ℝ) : ‖(E.component i).evalReal x‖ ≤ 1 :=
  ((E.component i).norm_evalReal_le x).trans (E.normBound_le i)

noncomputable def sampleModel (i : E.I) :
    NativeSampleModel w degree p sample (fun x => (E.component i).eval (sample x)) where
  L := native.L
  dim := native.dim
  model := native.model
  test := E.component i
  norm := E.normBound_le i
  complexity := E.complexity i
  eval _ := rfl

theorem coefficient_mass :
    (∑ _i : E.I, ‖(1 : ℂ)‖) ≤ Real.exp (verticalDecompositionBudget q) := by
  simpa using E.card_le

end VerticalExpansion
end Erdos3.NativeSampleModel

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_sampled_native_model {Ω T X σ I : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (w : σ → ℕ) (degree : ℕ) (complexity : ℝ) (sample : X → σ → ℤ)
    (twist : I → X → ℂ) (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 (K * (2 * C) / tau) ≤ sampledSliceSeminorm μ F slices tests g →
      ∃ (i : I) (G : X → ℂ), Nonempty (NativeSampleModel w degree complexity sample G) ∧
        beta ≤ ‖r.correlation g (fun x => star (twist i x) * G x)‖)
    (hexcess : r.excessMass (μ.siteLaw F) C ≤ ε)
    (b : X → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (e : X → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity sample twist) ∧
      b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ F slices tests e ≤ 2 * tau + 2 * K * (B + 2 / beta) * ε ∧
      (n : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let atoms := twistedNativeSampleFunctions w degree complexity sample twist
  let cap := max 1 (K * (2 * C) / tau)
  have hcap : 1 ≤ cap := le_max_left _ _
  have hdetector (g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ K * (2 * C) / tau)
      (hlarge : tau / B ^ 2 ≤ sampledSliceSeminorm μ F slices tests g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    have hunit (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
        (hX : (tau / B ^ 2) / cap ≤ sampledSliceSeminorm μ F slices tests v) :
        ∃ Q ∈ atoms, beta ≤ ‖r.correlation v Q‖ := by
      obtain ⟨i, G, hG, hcorr⟩ := hdetect v hv hX
      exact ⟨_, Or.inr ⟨i, G, hG, rfl⟩, hcorr⟩
    obtain ⟨Q, hQ, hc⟩ := detector_of_unit_detector r
      (sampledSliceSeminorm μ F slices tests) atoms (lt_of_lt_of_le zero_lt_one hcap)
      hunit g (fun x => (hg x).trans (le_max_right _ _)) hlarge
    have hscale : beta ≤ cap * beta := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap hbeta.le
    exact ⟨Q, hQ, hscale.trans hc⟩
  exact exists_sampled_slice_model μ F slices tests r hr
    (twistedNativeSampleFunctions_balanced twist) ⟨0, twistedNativeSampleFunctions_zero twist⟩
    (fun Q hQ x => twistedNativeSampleFunctions_norm twist htwist hQ x)
    hK hC hB hbeta htau hsize htests hdetector hexcess b hb

end Erdos3

end

end OAI
