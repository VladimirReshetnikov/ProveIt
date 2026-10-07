import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

def UnitIntervalValued (T : D.Niltest w) : Prop :=
  ∀ z, (T.observable z).im = 0 ∧ 0 ≤ (T.observable z).re ∧ (T.observable z).re ≤ 1

end RationalFilteredNilmanifold.Niltest

def CyclicNiltestUpperComparison.{u} (degree N : ℕ) [NeZero N]
    (P epsilon : ℝ) (f g : ZMod N → ℝ) : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s dim), s ≤ degree →
    ∀ (T : D.Niltest (fun _ : Unit => 1)), T.UnitIntervalValued → T.ComplexityLE P →
    (𝔼 x : ZMod N, (f x - g x) * (T.evalCyclic N (fun _ => x)).re) ≤ epsilon

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

noncomputable def idealQuotientOrbit {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit I hI g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQF]; exact q.adapted)

theorem idealQuotientOrbit_eval {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.idealQuotientOrbit I hI Q hQF g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitEval w x g) :=
  D.filtration.realQuotientPolynomialOrbit_eval I hI g x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

theorem exists_idealInvariant_niltest
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z : D.RealGroup, z.coord ∈ I.toSubmodule.baseChange ℝ → ∀ x,
      T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr (lieQuotientMap I (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = D.idealQuotientOrbit I hI Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound t d n H T.lipBound T.normBound ∧
      (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
        T.observable (QuotientGroup.mk x)) ∧
      (∀ x, S.eval x = T.eval x) ∧
      (T.UnitIntervalValued → S.UnitIntervalValued) := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap I) (lieQuotientMap_surjective I) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff I.toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := D.idealQuotientOrbit I hI Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound t d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl) }
  refine ⟨S, rfl, rfl, rfl, hf, ?_, ?_⟩
  · intro x
    exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
      (D.idealQuotientOrbit_eval I hI Q hQF T.orbit x)).trans (hf _)
  · intro hT z
    induction z using Quotient.inductionOn with
    | h z =>
      obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) z.coord
      let g : D.RealGroup := ⟨x⟩
      have hg : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g = z :=
        NilpotentLieBCHGroup.ext hx
      have hfg := hf g
      rw [hg] at hfg
      change (f (QuotientGroup.mk z)).im = 0 ∧ 0 ≤ (f (QuotientGroup.mk z)).re ∧
        (f (QuotientGroup.mk z)).re ≤ 1
      rw [hfg]
      exact hT (QuotientGroup.mk g)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def intervalClip (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun z => ((max 0 (min 1 (T.observable z).re) : ℝ) : ℂ)
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact (max_le (norm_nonneg _) ((min_le_right _ _).trans (Complex.re_le_norm _))).trans (T.norm_le z)
  lipschitz := by
    let := D.metricSpace
    have hr : LipschitzWith T.lipBound (fun z => (T.observable z).re) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (T.observable x).re (T.observable y).re ≤ dist (T.observable x) (T.observable y) := by
          simpa only [Real.dist_eq, dist_eq_norm, Complex.sub_re, Real.norm_eq_abs] using
            Complex.abs_re_le_norm (T.observable x - T.observable y)
        _ ≤ T.lipBound * dist x y := T.lipschitz.dist_le_mul x y
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp ((hr.const_min 1).const_max 0)

theorem intervalClip_unitInterval (T : D.Niltest w) : T.intervalClip.UnitIntervalValued := by
  intro z
  exact ⟨rfl, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem intervalClip_complexityLE (T : D.Niltest w) (p : ℝ) :
    T.intervalClip.ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem intervalClip_eval (T : D.Niltest w) (x : σ → ℤ)
    (hx : (T.eval x).im = 0 ∧ 0 ≤ (T.eval x).re ∧ (T.eval x).re ≤ 1) :
    T.intervalClip.eval x = T.eval x := by
  change ((max 0 (min 1 (T.eval x).re) : ℝ) : ℂ) = T.eval x
  apply Complex.ext
  · simp only [Complex.ofReal_re, min_eq_right hx.2.2, max_eq_right hx.2.1]
  · exact hx.1.symm

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

noncomputable def cyclicOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit w)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w
    (fun i => ((x i).val : ℤ)) g)

noncomputable def sectionNiltest
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) : D.Niltest w where
  orbit := g
  observable := fun z => (frozenRealSection F a z : ℂ)
  normBound := 1
  lipBound := M
  norm_le z := by
    have h := frozenRealSection_unit_interval F hF a z
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1, NNReal.coe_one] using h.2
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    cases a with
    | none =>
      change dist (0 : ℂ) 0 ≤ (M : ℝ) * dist x y
      rw [dist_self]
      positivity
    | some a =>
      change dist (F x a : ℂ) (F y a : ℂ) ≤ (M : ℝ) * dist x y
      simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
        (hLip a).dist_le_mul x y

theorem sectionNiltest_unit_interval
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a)) (a : Option Ξ) :
    (D.sectionNiltest g F hF M hLip a).UnitIntervalValued := by
  intro z
  exact ⟨rfl, frozenRealSection_unit_interval F hF a z⟩

theorem sectionNiltest_complexityLE
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hbudget : Real.log (3 + (M : ℝ)) ≤ p) :
    (D.sectionNiltest g F hF M hLip a).ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + (1 : ℝ) + (M : ℝ)) ≤ p
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num]
  exact hbudget

theorem sectionNiltest_evalCyclic_re
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    ((D.sectionNiltest g F hF M hLip a).evalCyclic N x).re =
      frozenRealSection F a (D.cyclicOrbitPoint g N x) := rfl

theorem sectionNiltest_none_eval
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (x : σ → ℤ) : (D.sectionNiltest g F hF M hLip none).eval x = 0 := rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CyclicNiltestShiftBound.{u} (degree N : ℕ) [NeZero N]
    (p error : ℝ) (a J : ZMod N → ℝ) (E : Finset (ZMod N)) : Prop :=
  ∀ h ∉ E, ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s dim), s ≤ degree →
    ∀ (T : D.Niltest (fun _ : Unit => 1)), T.UnitIntervalValued → T.ComplexityLE p →
    (𝔼 x : ZMod N, a x * J (x + h) * (T.evalCyclic N (fun _ => x)).re) ≤ error

theorem cyclicNiltestShiftBound_zero_of_constants.{u} {N : ℕ} [NeZero N]
    (a J : ZMod N → ℝ) (E : Finset (ZMod N)) {p error : ℝ}
    (hbound : ∀ h ∉ E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → realShiftCorrelation a J h * t ≤ error) :
    CyclicNiltestShiftBound.{u} 0 N p error a J E := by
  intro h hh L _ _ s dim _ _ _ _ D hs T hT _
  have hs0 : s = 0 := by omega
  subst s
  let t := (T.observable (QuotientGroup.mk (1 : D.RealGroup))).re
  have ht : 0 ≤ t ∧ t ≤ 1 := (hT _).2
  have heval (x : ZMod N) : (T.evalCyclic N (fun _ => x)).re = t := by
    exact congrArg Complex.re (RationalFilteredNilmanifold.Niltest.eval_step_zero D T _)
  simp_rw [heval]
  rw [← Finset.expect_mul]
  exact hbound h hh t ht.1 ht.2

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem UnitIntervalValued.norm_le_one {T : D.Niltest w} (hT : T.UnitIntervalValued) (x : D.Space) :
    ‖T.observable x‖ ≤ 1 := by
  have heq : ((T.observable x).re : ℂ) = T.observable x := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hT x).1.symm
  rw [← heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hT x).2.1]
  exact (hT x).2.2

noncomputable def withUnitBound (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) : D.Niltest w :=
  { T with normBound := 1, norm_le := hcap }

theorem withUnitBound_orbit (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) :
    (T.withUnitBound hcap).orbit = T.orbit := rfl

theorem withUnitBound_eval (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) (x : σ → ℤ) :
    (T.withUnitBound hcap).eval x = T.eval x := rfl

theorem withUnitBound_complexity (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.withUnitBound hcap).ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [Real.exp_add]
  have h := T.observable_budget hT
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg p)
  nlinarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

noncomputable def positiveLocalization : D.Niltest w where
  orbit := T.orbit
  observable z := (((T.observable z).re * psi z : ℝ) : ℂ)
  normBound := 1
  lipBound := T.lipBound + K
  norm_le z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT z).2.1 (hpsi z).1)]
    exact (mul_le_of_le_one_right (hT z).2.1 (hpsi z).2).trans (hT z).2.2
  lipschitz := by
    let := D.metricSpace
    have ht : LipschitzWith T.lipBound (fun z => (T.observable z).re) := by
      simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp T.lipschitz
    have hproduct := bounded_weight_cutoff_lipschitz (fun z => (T.observable z).re) psi
      (B := 1)
      (fun z => by rw [abs_of_nonneg (hT z).2.1]; exact (hT z).2.2)
      (fun z => by rw [abs_of_nonneg (hpsi z).1]; exact (hpsi z).2) ht hLip
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hproduct

theorem positiveLocalization_orbit :
    (T.positiveLocalization hT psi hpsi K hLip).orbit = T.orbit := rfl

theorem positiveLocalization_unit_interval :
    (T.positiveLocalization hT psi hpsi K hLip).UnitIntervalValued := by
  intro z
  exact ⟨rfl, mul_nonneg (hT z).2.1 (hpsi z).1,
    (mul_le_of_le_one_right (hT z).2.1 (hpsi z).2).trans (hT z).2.2⟩

theorem positiveLocalization_eval_re (x : σ → ℤ) :
    ((T.positiveLocalization hT psi hpsi K hLip).eval x).re =
      (T.eval x).re * psi (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w x T.orbit)) := rfl

theorem positiveLocalization_support :
    tsupport (T.positiveLocalization hT psi hpsi K hLip).observable ⊆ tsupport psi := by
  apply closure_mono
  intro z hz
  change psi z ≠ 0
  intro hzero
  apply hz
  change (((T.observable z).re * psi z : ℝ) : ℂ) = 0
  rw [hzero, mul_zero, Complex.ofReal_zero]

theorem positiveLocalization_complexity {p : ℝ} (hp : 0 ≤ p)
    (hcomplexity : T.ComplexityLE p) (hK : (K : ℝ) ≤ Real.exp p) :
    (T.positiveLocalization hT psi hpsi K hLip).ComplexityLE (p + 4) := by
  refine ⟨hcomplexity.1.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + ((T.lipBound + K : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [NNReal.coe_add, Real.exp_add]
  have hbudget := observable_budget hcomplexity
  have hnorm := T.normBound.coe_nonneg
  have hone := Real.one_le_exp hp
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg p)
  nlinarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_idealInvariant_niltest_budget (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]
      (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
      (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
      (hQF : Q.filtration = D.filtration.quotientLie I hI)
      (_hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p) →
      (∀ z : D.RealGroup, z.coord ∈ I.toSubmodule.baseChange ℝ → ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = D.idealQuotientOrbit I hI Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + 2) ^ C) ∧
        (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
          (NilpotentLieBCHGroup.realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
          T.observable (QuotientGroup.mk x)) ∧
        (∀ x, S.eval x = T.eval x) ∧ (T.UnitIntervalValued → S.UnitIntervalValued) := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp t
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((X + 1 + Polynomial.C a) ^ a + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ s d n D I _ _ _ _ hI Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hObs, hSe, hPos⟩ := D.exists_idealInvariant_niltest I hI Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + 2) ^ C := by
    simpa [r, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩,
    hObs, hSe, hPos⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
