import OAI.Combinatorics.Progressions.Estimates.PinnedSectionMeans
import OAI.Combinatorics.Progressions.Estimates.SampledSliceFixedModelPartners

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withOrbit (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) : D.Niltest v where
  orbit := g
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le := T.norm_le
  lipschitz := T.lipschitz

theorem withOrbit_complexity (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withOrbit g).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem withOrbit_eval (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withOrbit g).eval x = T.observable
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x g)) := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def constantGroupOrbit (g : F.Group) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (monomial (R := ℚ) 0 g.coord)
    ((F.mem_adaptedSubmodule w _).mp
      (F.monomial_mem_adaptedSubmodule w 0 (by
        simp only [map_zero]
        exact F.antitone (Nat.zero_le 1) (by simp [F.one_eq_top]))))

@[simp] theorem polynomialOrbitEval_constantGroupOrbit (g : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.constantGroupOrbit w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp [polynomialOrbitEval_coord, constantGroupOrbit, eval_monomial]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withLeftTranslatedOrbit (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) : D.Niltest v :=
  T.withOrbit (D.filtration.realification.constantGroupOrbit v g * orbit)

@[simp] theorem withLeftTranslatedOrbit_observable (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) :
    (T.withLeftTranslatedOrbit g orbit).observable = T.observable := rfl

@[simp] theorem withLeftTranslatedOrbit_complexity (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withLeftTranslatedOrbit g orbit).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

@[simp] theorem withLeftTranslatedOrbit_eval (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withLeftTranslatedOrbit g orbit).eval x = T.observable
      (g • QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x orbit)) := by
  rw [withLeftTranslatedOrbit, withOrbit_eval, map_mul,
    NilpotentLieFiltration.polynomialOrbitEval_constantGroupOrbit]
  rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L X Y Ω T : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L 0 d} {w : Y → ℕ}

theorem exists_step_zero_ambient_realization (reference : D.Niltest w)
    (localTests : Ω → D.Niltest w)
    (hcommon : ∀ a, (localTests a).observable = reference.observable)
    {p : ℝ} (hcomplexity : reference.ComplexityLE p)
    (hunit : reference.UnitIntervalValued) :
    ∃ ambient : D.Niltest (fun _ : X => 1),
      ambient.observable = reference.observable ∧ ambient.UnitIntervalValued ∧
      ambient.ComplexityLE p ∧
      ∀ a x y, ambient.eval x = (localTests a).eval y := by
  refine ⟨reference.withOrbit 1, rfl, hunit, hcomplexity, ?_⟩
  intro a x y
  rw [eval_step_zero, eval_step_zero, hcommon]
  rfl

theorem exists_step_zero_ambient_realization_preserving_scores
    [Fintype Ω] [Fintype T]
    (reference : D.Niltest w) (localTests : Ω → D.Niltest w)
    (hcommon : ∀ a, (localTests a).observable = reference.observable)
    {p : ℝ} (hcomplexity : reference.ComplexityLE p)
    (hunit : reference.UnitIntervalValued)
    (outer : FiniteProbabilityWeights Ω) (productive retained : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T)
    (localPoint : Ω → T → Y → ℤ) (physical : Ω → T → X → ℤ)
    (score : Ω → T → ℝ) (massThreshold correlationThreshold : ℝ)
    (hretained : retained ⊆ productive) (hmass : massThreshold ≤ outer.mass retained)
    (hscore : ∀ a ∈ retained, correlationThreshold ≤
      (localLaw a).mean (fun t => score a t * ((localTests a).eval (localPoint a t)).re)) :
    ∃ ambient : D.Niltest (fun _ : X => 1),
      ambient.observable = reference.observable ∧ ambient.UnitIntervalValued ∧
      ambient.ComplexityLE p ∧ retained ⊆ productive ∧
      massThreshold ≤ outer.mass retained ∧
      ∀ a ∈ retained, correlationThreshold ≤
        (localLaw a).mean (fun t => score a t * (ambient.eval (physical a t)).re) := by
  obtain ⟨ambient, hobservable, hunit', hcomplexity', heval⟩ :=
    exists_step_zero_ambient_realization (X := X)
      reference localTests hcommon hcomplexity hunit
  refine ⟨ambient, hobservable, hunit', hcomplexity', hretained, hmass, ?_⟩
  intro a ha
  have hvalues : (fun t => score a t * (ambient.eval (physical a t)).re) =
      (fun t => score a t * ((localTests a).eval (localPoint a t)).re) := by
    funext t
    rw [heval a (physical a t) (localPoint a t)]
  rw [hvalues]
  exact hscore a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

variable {L Y Ω T X K : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : Y → ℕ}

noncomputable def localNiltestPartnerWeight
    (tests : Ω → K → D.Niltest w) (point : Ω → T → Y → ℤ) (p : ℝ) :
    Ω → K → T → ℂ :=
  fun a k t => (Real.exp (-p) : ℂ) * (tests a k).eval (point a t)

theorem localNiltestPartnerWeight_norm_le
    (tests : Ω → K → D.Niltest w) (point : Ω → T → Y → ℤ) (p : ℝ)
    (hcomplexity : ∀ a k, (tests a k).ComplexityLE p) (a : Ω) (k : K) (t : T) :
    ‖localNiltestPartnerWeight tests point p a k t‖ ≤ 1 := by
  rw [localNiltestPartnerWeight, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left
      ((tests a k).eval_budget (hcomplexity a k) _) (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem localNiltestPartnerWeight_mean_norm [Fintype T]
    (tests : Ω → K → D.Niltest w) (point : Ω → T → Y → ℤ) (p : ℝ)
    (a : Ω) (k : K) (S : Finset T) (v : T → ℂ) :
    ‖𝔼 t ∈ S, v t * localNiltestPartnerWeight tests point p a k t‖ =
      Real.exp (-p) * ‖𝔼 t ∈ S, v t * (tests a k).eval (point a t)‖ := by
  have heq : (fun t => v t * localNiltestPartnerWeight tests point p a k t) =
      (fun t => (Real.exp (-p) : ℂ) * (v t * (tests a k).eval (point a t))) := by
    funext t
    dsimp only [localNiltestPartnerWeight]
    ring
  rw [heq, ← Finset.mul_expect, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

theorem exists_local_niltest_fixed_native_partners
    {I σ Θ : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype K] [Fintype I] [Nonempty I]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (physical : Ω → T → X) (slices : Ω → K → Finset T)
    (tests : Ω → K → D.Niltest w) (point : Ω → T → Y → ℤ)
    (p : ℝ) (hcomplexity : ∀ a k, (tests a k).ComplexityLE p)
    (hS : ∀ a k, (slices a k).Nonempty) {cap : ℝ}
    (hsize : ∀ a k, (Fintype.card T : ℝ) / (slices a k).card ≤ cap)
    (v e : X → ℂ) (Q : I → X → ℂ) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • Q i) + e)
    {M kappa : ℝ} (hM : 0 < M) (hkappa : 0 < kappa)
    (hc : (∑ i, ‖c i‖) ≤ M) (hmass : kappa ≤ outer.mass productive)
    (herror : (Fintype.card K : ℝ) *
      sampledSliceSeminorm outer physical slices
        (localNiltestPartnerWeight tests point p) e ≤ kappa * Real.exp (-2 * p) / 8)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hQ : ∀ i, Q i ∈ twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hscore : ∀ a ∈ productive, ∀ k, Real.exp (-p) ≤
      ‖𝔼 t ∈ slices a k, v (physical a t) * (tests a k).eval (point a t)‖) :
    ∃ (fixedTwist : K → Θ) (nativeValue : K → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      (3 * kappa / 4) / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-p) / (2 * M) ≤
        ‖𝔼 t ∈ slices a k,
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            (tests a k).eval (point a t)‖ := by
  have herr : (∑ _k : K, sampledSliceSeminorm outer physical slices
      (localNiltestPartnerWeight tests point p) e) ≤ kappa * Real.exp (-2 * p) / 8 := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using herror
  have hscale : Real.exp (-p) * Real.exp (-p) = Real.exp (-2 * p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨fixedTwist, nativeValue, native, retained, hsub, hpos, hretained, hlocal⟩ :=
    exists_fixed_sampled_slice_native_partners outer productive physical slices
      (localNiltestPartnerWeight tests point p) (fun _ k => k) hS hsize
      (localNiltestPartnerWeight_norm_le tests point p hcomplexity)
      (fun _ : K => v) (fun _ : K => e) (fun _ : K => Q) (fun _ : K => c)
      (fun _ => hmodel) (Real.exp_pos _) hM (fun _ => hc) hmass herr hkappa
      nativeWeight degree budget sample twist (fun _ => hQ) (by
        intro a ha k
        rw [localNiltestPartnerWeight_mean_norm, ← hscale]
        exact mul_le_mul_of_nonneg_left (hscore a ha k) (Real.exp_nonneg _))
  refine ⟨fixedTwist, nativeValue, native, retained, hsub, hpos, ?_, ?_⟩
  · simpa only [Finset.prod_const, Finset.card_univ] using hretained
  · intro a ha k
    have h := hlocal a ha k
    rw [localNiltestPartnerWeight_mean_norm, ← hscale] at h
    have heq : Real.exp (-p) * Real.exp (-p) / (2 * M) =
        Real.exp (-p) * (Real.exp (-p) / (2 * M)) := by ring
    rw [heq] at h
    exact le_of_mul_le_mul_left h (Real.exp_pos (-p))

end Erdos3

end

end OAI
