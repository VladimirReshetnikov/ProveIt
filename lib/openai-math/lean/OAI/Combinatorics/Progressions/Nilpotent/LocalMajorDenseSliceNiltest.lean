import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Complex.Circle
import OAI.Combinatorics.Progressions.Estimates.VectorApproximationPrecomposition
import OAI.Combinatorics.Progressions.Estimates.WeightedTwistedTranslationLipschitz
import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget
import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
import OAI.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
import OAI.Combinatorics.Progressions.Polynomial.SlowPolynomialSliceLogCost
import OAI.Combinatorics.Progressions.Polynomial.WeightedTranslationLatticePhase

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def scaleComplex (T : D.Niltest w) (c : ℂ) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => c * T.observable x
  normBound := ‖c‖₊ * T.normBound
  lipBound := ‖c‖₊ * T.lipBound
  norm_le x := by
    simpa only [norm_mul, NNReal.coe_mul, coe_nnnorm] using
      mul_le_mul_of_nonneg_left (T.norm_le x) (norm_nonneg c)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← mul_sub, norm_mul, NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left (T.lipschitz.dist_le_mul x y) (norm_nonneg c)

theorem scaleComplex_eval (T : D.Niltest w) (c : ℂ) (x : σ → ℤ) :
    (T.scaleComplex c).eval x = c * T.eval x := rfl

theorem scaleComplex_evalCyclic (T : D.Niltest w) (c : ℂ) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.scaleComplex c).evalCyclic N x = c * T.evalCyclic N x := rfl

theorem scaleComplex_norm (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (T.scaleComplex c).normBound ≤ T.normBound := by
  change ‖c‖₊ * T.normBound ≤ T.normBound
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hc)

theorem scaleComplex_complexity (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.scaleComplex c).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + ‖c‖ * (T.normBound : ℝ) + ‖c‖ * (T.lipBound : ℝ)) ≤ p
  have hn := mul_le_mul_of_nonneg_right hc T.normBound.coe_nonneg
  have hl := mul_le_mul_of_nonneg_right hc T.lipBound.coe_nonneg
  exact (Real.log_le_log (by positivity) (by linarith)).trans hT.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct Manifold ContDiff

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def evalReal (T : D.Niltest w) (x : σ → ℝ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x T.orbit))

theorem evalReal_integer (T : D.Niltest w) (x : σ → ℤ) :
    T.evalReal (fun i => (x i : ℝ)) = T.eval x := by
  unfold evalReal eval
  rw [NilpotentLieFiltration.polynomialOrbitRealEval_integer]

theorem norm_evalReal_le (T : D.Niltest w) (x : σ → ℝ) : ‖T.evalReal x‖ ≤ T.normBound :=
  T.norm_le _

theorem continuous_evalReal [Fintype σ] (T : D.Niltest w) : Continuous T.evalReal := by
  let := D.metricSpace
  let := NilpotentLieBCHGroup.basisChartedSpace
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hp := D.filtration.realification.contMDiff_polynomialOrbitRealEval
    (D.basis.baseChange ℝ) w T.orbit ⊤
  exact T.lipschitz.continuous.comp (QuotientGroup.continuous_mk.comp hp.continuous)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def expNormalize (T : D.Niltest w) (p : ℝ) : D.Niltest w :=
  T.scaleComplex (Real.exp (-p) : ℂ)

theorem expNormalize_norm (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).normBound ≤ 1 := by
  have hb := T.observable_budget hT
  have hl := T.lipBound.coe_nonneg
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith
  change ‖(Real.exp (-p) : ℂ)‖₊ * T.normBound ≤ 1
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, coe_nnnorm, NNReal.coe_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  calc
    _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem expNormalize_complexity (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).ComplexityLE p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  apply T.scaleComplex_complexity _ hT
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem expNormalize_eval (T : D.Niltest w) (p : ℝ) (x : σ → ℤ) :
    (T.expNormalize p).eval x = (Real.exp (-p) : ℂ) * T.eval x := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_bounded_niltest_pair_sum {J σ L K : Type*} [Fintype J] [Nonempty J]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (gD : D.filtration.realification.PolynomialOrbit w)
    (gE : E.filtration.realification.PolynomialOrbit w)
    (A : J → D.Niltest w) (B : J → E.Niltest w) (c : J → ℂ) {p : ℝ}
    (hAnorm : ∀ j, (A j).normBound ≤ 1) (hBnorm : ∀ j, (B j).normBound ≤ 1)
    (hA : ∀ j, (A j).ComplexityLE p) (hB : ∀ j, (B j).ComplexityLE p)
    (hAg : ∀ j, (A j).orbit = gD) (hBg : ∀ j, (B j).orbit = gE)
    (hc : ∀ j, ‖c j‖ ≤ 2) :
    ∃ N : ℕ, 0 < N ∧ N = 2 * Fintype.card J ∧
      ∃ (A' : Fin N → D.Niltest w) (B' : Fin N → E.Niltest w),
        (∀ j, (A' j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
        (∀ j, (A' j).ComplexityLE p) ∧ (∀ j, (B' j).ComplexityLE p) ∧
        (∀ j, (A' j).orbit = gD) ∧ (∀ j, (B' j).orbit = gE) ∧
        ∀ x, ∑ j, (A' j).eval x * (B' j).eval x =
          ∑ j, ((A j).eval x * (B j).eval x) * c j := by
  classical
  let f := (Fintype.equivFin (Bool × J)).symm
  let A' (j : Fin (Fintype.card (Bool × J))) :=
    (A (f j).2).scaleComplex (c (f j).2 / 2)
  let B' (j : Fin (Fintype.card (Bool × J))) := B (f j).2
  refine ⟨Fintype.card (Bool × J), Fintype.card_pos, ?_, A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_bool]
  · intro j
    exact ((A (f j).2).scaleComplex_norm (norm_complex_half_le_one (hc (f j).2))).trans (hAnorm _)
  · intro j
    exact hBnorm _
  · intro j
    exact (A (f j).2).scaleComplex_complexity (norm_complex_half_le_one (hc (f j).2)) (hA _)
  · intro j
    exact hB _
  · intro j
    exact hAg _
  · intro j
    exact hBg _
  · intro x
    exact (f.sum_comp (fun j => (c j.2 / 2 * (A j.2).eval x) * (B j.2).eval x)).trans
      (sum_double_half_products (fun j => (A j).eval x) (fun j => (B j).eval x) c)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def phaseShift (T : D.Niltest w) (a : ℝ) : D.Niltest w :=
  T.scaleComplex (Real.fourierChar a : ℂ)

@[simp] theorem phaseShift_orbit (T : D.Niltest w) (a : ℝ) :
    (T.phaseShift a).orbit = T.orbit := rfl

@[simp] theorem phaseShift_normBound (T : D.Niltest w) (a : ℝ) :
    (T.phaseShift a).normBound = T.normBound := by
  have hn : ‖(Real.fourierChar a : ℂ)‖₊ = 1 := by
    apply NNReal.coe_injective
    exact Circle.norm_coe _
  change ‖(Real.fourierChar a : ℂ)‖₊ * T.normBound = T.normBound
  rw [hn, one_mul]

@[simp] theorem phaseShift_lipBound (T : D.Niltest w) (a : ℝ) :
    (T.phaseShift a).lipBound = T.lipBound := by
  have hn : ‖(Real.fourierChar a : ℂ)‖₊ = 1 := by
    apply NNReal.coe_injective
    exact Circle.norm_coe _
  change ‖(Real.fourierChar a : ℂ)‖₊ * T.lipBound = T.lipBound
  rw [hn, one_mul]

@[simp] theorem phaseShift_complexity_iff (T : D.Niltest w) (a p : ℝ) :
    (T.phaseShift a).ComplexityLE p ↔ T.ComplexityLE p := by
  simp only [ComplexityLE, phaseShift_normBound, phaseShift_lipBound]

@[simp] theorem phaseShift_eval (T : D.Niltest w) (a : ℝ) (u : σ → ℤ) :
    (T.phaseShift a).eval u = (Real.fourierChar a : ℂ) * T.eval u := rfl

@[simp] theorem phaseShift_evalReal (T : D.Niltest w) (a : ℝ) (u : σ → ℝ) :
    (T.phaseShift a).evalReal u = (Real.fourierChar a : ℂ) * T.evalReal u := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalTorus

instance zeroAlgebraSubsingleton : Subsingleton (Algebra 0) :=
  inferInstanceAs (Subsingleton (Fin 0 → ℚ))

def trivialFiltration (s : ℕ) : NilpotentLieFiltration (Algebra 0) s where
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  one_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal := by
    apply le_antisymm _ bot_le
    intro x _
    simpa only [Submodule.mem_bot] using (Subsingleton.elim x 0)

theorem trivialFiltration_basis_layers (s j : ℕ) :
    (trivialFiltration s).layer j = Submodule.span ℚ ((basis 0) '' {_i : Fin 0 | j ≤ (0 : ℕ)}) := by
  ext x
  rw [Subsingleton.elim x 0]
  simp only [Submodule.zero_mem]

theorem trivial_lattice_inner_grid (s : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) := by
  intro x _
  trivial

theorem trivial_lattice_outer_grid (s : ℕ) :
    bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) ⊆ denominatorGrid 1 := by
  intro x _
  exact ⟨0, fun i => Fin.elim0 i⟩

noncomputable def trivialNilmanifold (s : ℕ) : RationalFilteredNilmanifold (Algebra 0) s 0 :=
  (trivialFiltration s).ofAdaptedBasis (basis 0) (fun _ => 0) (trivialFiltration_basis_layers s)
    ⊤ 1 (by omega) (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s)

theorem trivialNilmanifold_geometry (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (trivialNilmanifold s).GeometryComplexityLE p := by
  apply (trivialFiltration s).ofAdaptedBasis_geometry (basis 0) (fun _ => 0)
    (trivialFiltration_basis_layers s) ⊤ 1 (by omega)
    (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s) hp (by simpa using hp)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i
    exact Fin.elim0 i

theorem trivialNilmanifold_const_one_complexity (s : ℕ) {σ : Type*} (w : σ → ℕ) {p : ℝ}
    (hp : 2 ≤ p) :
    (RationalFilteredNilmanifold.Niltest.const (trivialNilmanifold s) w 1).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s (by linarith), ?_⟩
  change Real.log (2 + (‖(1 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_one, NNReal.coe_one, add_zero]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at *
  linarith

end Erdos3.RationalTorus

end

section

namespace Erdos3

open MvPolynomial

variable {U : Type*}

noncomputable def zeroDegreePolynomialPhaseNiltest (w : U → ℕ)
    (P : MvPolynomial U ℝ) : (RationalTorus.trivialNilmanifold 0).Niltest w :=
  RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) w
    (Real.fourierChar (P.coeff 0) : ℂ)

@[simp] theorem zeroDegreePolynomialPhaseNiltest_normBound (w : U → ℕ)
    (P : MvPolynomial U ℝ) :
    (zeroDegreePolynomialPhaseNiltest w P).normBound = 1 := by
  apply NNReal.eq
  exact Circle.norm_coe _

theorem zeroDegreePolynomialPhaseNiltest_complexity (w : U → ℕ)
    (P : MvPolynomial U ℝ) {p : ℝ} (hp : 2 ≤ p) :
    (zeroDegreePolynomialPhaseNiltest w P).ComplexityLE p := by
  refine ⟨RationalTorus.trivialNilmanifold_geometry 0 (by linarith), ?_⟩
  change Real.log (2 + (‖(Real.fourierChar (P.coeff 0) : ℂ)‖₊ : ℝ) + 0) ≤ p
  simp only [coe_nnnorm, Circle.norm_coe, add_zero]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at h ⊢
  linarith

theorem zeroDegreePolynomialPhaseNiltest_evalReal (w : U → ℕ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ 0) (u : U → ℝ) :
    (zeroDegreePolynomialPhaseNiltest w P).evalReal u =
      (Real.fourierChar (eval u P) : ℂ) := by
  have heq : P = C (P.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hP)
  change (Real.fourierChar (P.coeff 0) : ℂ) = (Real.fourierChar (eval u P) : ℂ)
  conv_rhs => rw [heq, eval_C]

theorem exists_zeroDegreePolynomialPhaseNiltest (w : U → ℕ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ 0) :
    ∃ T : (RationalTorus.trivialNilmanifold 0).Niltest w,
      T.normBound = 1 ∧ T.ComplexityLE 2 ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) :=
  ⟨zeroDegreePolynomialPhaseNiltest w P,
    zeroDegreePolynomialPhaseNiltest_normBound w P,
    zeroDegreePolynomialPhaseNiltest_complexity w P le_rfl,
    zeroDegreePolynomialPhaseNiltest_evalReal w P hP⟩

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedTranslationBufferedObservable (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) :
    (weightedTranslationNilmanifold w d hw hwd).Space → ℂ :=
  bufferedTranslationQuotientPhase Ψ D₀ ∘ weightedTranslationPhaseQuotientMap w d hw hwd

@[simp] theorem weightedTranslationBufferedObservable_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀ (QuotientGroup.mk g) =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd g) := rfl

theorem weightedTranslationBufferedObservable_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : (weightedTranslationNilmanifold w d hw hwd).Space) :
    ‖weightedTranslationBufferedObservable w d hw hwd Ψ D₀ g‖ ≤ 1 :=
  bufferedTranslationQuotientPhase_norm_le_one Ψ D₀ _

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationBufferedObservable_lipschitz
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M) :
    letI := (weightedTranslationNilmanifold w d hw hwd).metricSpace
    LipschitzWith (2 * bufferedTranslationTermLip w d Ψ M)
      (weightedTranslationBufferedObservable w d hw hwd Ψ D₀) := by
  let e := (weightedOrderedBasis w d hw).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift
    (weightedTranslationNilmanifold w d hw hwd).realLattice
    (weightedTranslationNilmanifold w d hw hwd).realLattice_closed_discrete.1
    (weightedTranslationBufferedObservable w d hw hwd Ψ D₀)
    (bufferedTranslationPhase_lipschitz w d hw hd hwd Ψ D₀ M hdegree hD)

noncomputable def weightedTranslationBufferedNiltest {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) :
    (weightedTranslationNilmanifold w d hw hwd).Niltest ω where
  orbit := q
  observable := weightedTranslationBufferedObservable w d hw hwd Ψ D₀
  normBound := 1
  lipBound := 2 * bufferedTranslationTermLip w d Ψ M
  norm_le := weightedTranslationBufferedObservable_norm_le_one w d hw hwd Ψ D₀
  lipschitz := weightedTranslationBufferedObservable_lipschitz w d hw hwd hd Ψ D₀ M hdegree hD

@[simp] theorem weightedTranslationBufferedNiltest_eval {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℤ) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).eval t =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω t q)) := rfl

@[simp] theorem weightedTranslationBufferedNiltest_evalReal {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℝ) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).evalReal t =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval ω t q)) := rfl

theorem weightedTranslationBufferedNiltest_complexity {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) {p : ℝ}
    (hgeometry : (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p)
    (hbound : Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).ComplexityLE p := by
  refine ⟨hgeometry, ?_⟩
  simpa only [weightedTranslationBufferedNiltest, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbound

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

def weight : Fin 0 → ℕ := fun _ => 1

theorem weight_pos : ∀ i, 0 < weight i := fun i => Fin.elim0 i

theorem weight_le (s : ℕ) : ∀ i, weight i ≤ s := fun i => Fin.elim0 i

noncomputable local instance phaseBasisFintype (s : ℕ) :
    Fintype (WeightedBasisIndex weight s) := by
  let := weightedBasisIndex_finite weight s weight_pos
  exact Fintype.ofFinite _

noncomputable abbrev nilmanifold (s : ℕ) :=
  weightedTranslationNilmanifold weight s weight_pos (weight_le s)

noncomputable def budget (s : ℕ) : ℝ :=
  max ((0 + (0 + 1)^s + s.factorial + 2*s + 1 : ℕ) : ℝ)
    (Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)))

theorem two_le_budget (s : ℕ) : 2 ≤ budget s := by
  apply le_trans _ (le_max_left _ _)
  have hf := Nat.factorial_pos s
  have hn : 2 ≤ 0 + (0 + 1)^s + s.factorial + 2*s + 1 := by
    simp only [zero_add, one_pow]
    omega
  exact_mod_cast hn

theorem nilmanifold_geometry (s : ℕ) : (nilmanifold s).GeometryComplexityLE (budget s) := by
  apply RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    (weightedTranslationNilmanifold_complexity_budget weight s weight_pos (weight_le s))
  simpa only [Fintype.card_fin, budget] using le_max_left
    (((0 + (0 + 1)^s + s.factorial + 2*s + 1 : ℕ) : ℝ))
    (Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)))

theorem specialize_rename {U : Type*} (P : MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u =
      C (eval u P) := by
  simp only [specializeMajorParameters, RingHom.comp_id, eval₂Hom_rename]
  change eval₂ C (fun i => C (u i)) P = C (eval u P)
  exact (eval₂_comp C u P).symm

theorem exists_phase_orbit {U : Type*} (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ q : (nilmanifold s).filtration.realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom weight s (weight_le s)
          ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
            (fun _ : U => 1) u q) = ⟨0, C (eval u P)⟩ := by
  have hslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u ∈
        weightedSupportLT weight s := by
    intro u α _
    have hα : α = 0 := Subsingleton.elim _ _
    change Finsupp.weight weight α < s
    simpa only [hα, map_zero] using hs
  obtain ⟨q, hq⟩ := exists_translation_coordinate_polynomialOrbit weight s weight_pos
    (weight_le s) (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)
    (rename Sum.inl P)
    (majorParameterRename_degree (fun _ : U => 1) weight
      ((mem_weightedSupportLE_one_iff P s).mpr hP)) hslot
  refine ⟨q, fun u => ?_⟩
  change bchRealTranslationHom weight s (weight_le s)
    ((weightedFiltration weight s (weight_le s)).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u q) = _
  rw [hq u, specialize_rename]
  rfl

variable {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]

theorem exists_niltest {U : Type*} (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ T : (nilmanifold s).Niltest (fun _ : U => 1),
      T.normBound = 1 ∧ T.ComplexityLE (budget s) ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) := by
  obtain ⟨q, hq⟩ := exists_phase_orbit s hs P hP
  let Ψ := localTentKernel 0 8 (by decide)
  let T := weightedTranslationBufferedNiltest weight s weight_pos (weight_le s)
    (fun _ : U => 1) hs Ψ 0 0 (by simp) (by simp [realPolynomialMass]) q
  refine ⟨T, rfl, ?_, ?_⟩
  · apply weightedTranslationBufferedNiltest_complexity
    · exact nilmanifold_geometry s
    · exact le_max_right _ _
  · intro u
    change bufferedTranslationPhase Ψ 0 (bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
        (fun _ : U => 1) u q)) = _
    rw [hq u]
    rw [bufferedTranslationPhase_eq_chart Ψ 0 _ 0 (fun i => Fin.elim0 i)]
    have hd : ∀ x y : Fin 0 → ℝ, dist x y = 0 := by
      intro x y
      rw [Subsingleton.elim x y, dist_self]
    simp [bufferedTranslationTerm, translationPhaseArgument, Ψ, localTentKernel, hd]

theorem exists_niltest_of_degree {U : Type*}
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ T : (nilmanifold s).Niltest (fun _ : U => 1),
      T.normBound = 1 ∧ T.ComplexityLE (budget s) ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) := by
  by_cases hs : 0 < s
  · exact exists_niltest hs P hP
  · have hs : s = 0 := by omega
    subst s
    let T := RationalFilteredNilmanifold.Niltest.const (nilmanifold 0)
      (fun _ : U => 1) (Real.fourierChar (P.coeff 0) : ℂ)
    have hn : T.normBound = 1 := by
      apply NNReal.eq
      exact Circle.norm_coe _
    refine ⟨T, hn, ⟨nilmanifold_geometry 0, ?_⟩, ?_⟩
    · rw [hn]
      change Real.log (2 + (1 : ℝ) + 0) ≤ budget 0
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at hl ⊢
      exact hl.trans (two_le_budget 0)
    · intro u
      have heq : P = C (P.coeff 0) :=
        totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hP)
      change (Real.fourierChar (P.coeff 0) : ℂ) = (Real.fourierChar (eval u P) : ℂ)
      conv_rhs => rw [heq, eval_C]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_localMajor_slice_niltest
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      (𝔼 x, f x) ≤ (𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        1 - 2 * Real.pi * δ ≤ ‖𝔼 j : (∀ i, Fin (A.length i)),
          (Real.fourierChar (eval (fun i => ((A.point j i).val : ℝ)) P) : ℂ) *
            star (T.eval (fun i => ((j i).val : ℤ)))‖ := by
  intro K ρ hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hKρ : K * ρ ≤ δ := by
    have hle := (le_div_iff₀ (by linarith : 0 < K + 1)).mp
      (min_le_right (1 : ℝ) (δ / (K + 1)))
    change ρ * (K + 1) ≤ δ at hle
    nlinarith
  obtain ⟨A, hA, hscore, hslow⟩ := exists_slowPolynomial_residueSlice N hq hρ
    (min_le_left _ _) hM hlarge E hE hcoeff f
  let r : U → ℤ := fun i => (A.start i : ℤ)
  let v : (∀ i, Fin (A.length i)) → U → ℤ := fun j i => ((j i).val : ℤ)
  let Q := localMajorLowerPhase n q r P
  obtain ⟨T, hnorm, hbudget, hT⟩ := OrdinaryPolynomialPhase.exists_niltest_of_degree
    Q (localMajorLowerPhase_totalDegree_le n q r P hP)
  refine ⟨A, hA, hscore, T, hnorm, hbudget, ?_⟩
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, (hA i).1⟩⟩
  have hpoint (j : ∀ i, Fin (A.length i)) :
      (fun i => ((r i + (q : ℤ) * v j i : ℤ) : ℝ)) =
        (fun i => ((A.point j i).val : ℝ)) := by
    funext i
    simp only [r, v, ResidueBoxSlice.point, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
  have hlocal := (localMajorPhaseCorrelation
    (FiniteProbabilityWeights.uniform (∀ i, Fin (A.length i))) v n q hq r P E R hP htop hR
    (eval (fun i => (A.start i : ℝ)) E) δ (by
      intro j _
      rw [hpoint j]
      exact (hslow j).trans (by simpa only [K, Nat.cast_add, Nat.cast_one] using hKρ))).2
  rw [FiniteProbabilityWeights.uniform_complexMean] at hlocal
  have heval (j : ∀ i, Fin (A.length i)) : T.eval (v j) =
      (Real.fourierChar (eval (fun i => (v j i : ℝ)) Q) : ℂ) := by
    rw [← T.evalReal_integer, hT]
  simpa only [hpoint, heval, Q, v] using hlocal

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_localMajor_dense_slice_niltest
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        1 - 2 * Real.pi * δ ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  intro K ρ hlarge
  obtain ⟨A, hA, hscore, T, hnorm, hbudget, hcorr⟩ := exists_localMajor_slice_niltest
    N q hq P E R hP hE htop hR M δ hM hδ hcoeff
    (fun x => f (fun i => ((x i).val : ℤ))) hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  refine ⟨A, A.isDenseCommonStrideBox hq hρ (fun i => (hA i).1)
    (fun i => (hA i).2), ?_, T, hnorm, hbudget, ?_⟩
  · rw [A.expect_integerPoints hq]
    exact hscore
  · rw [A.expect_integerPoints hq]
    simp only [A.commonStrideIndex_integerPoint hq, ResidueBoxSlice.integerPoint,
      Int.cast_natCast]
    exact hcorr

theorem major_phase_nine_tenths :
    1 - 2 * Real.pi * (1 / (20 * Real.pi)) = (9 / 10 : ℝ) := by
  field_simp
  ring

theorem exists_localMajor_dense_slice_niltest_nine_tenths
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 ((1 / (20 * Real.pi)) / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  simpa only [major_phase_nine_tenths] using exists_localMajor_dense_slice_niltest
    N q hq P E R hP hE htop hR M (1 / (20 * Real.pi)) hM (by positivity) hcoeff f

theorem exists_localMajor_dense_slice_niltest_early
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M p : ℝ) (hM : 0 ≤ M) (hp : 1 ≤ p)
    (hdim : (Fintype.card U : ℝ) ≤ p) (hMexp : M ≤ Real.exp p)
    (hqexp : (q : ℝ) ≤ Real.exp p)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ)
    (hN : ∀ i, Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) :
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N ((p + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  let ρ := slowPolynomialSliceRadius (n + 1) (Fintype.card U) M
  have hρ : 0 < ρ := slowPolynomialSliceRadius_pos _ _ hM
  have hcost : Real.log (4 * (q : ℝ) / ρ) ≤ (p + (n + 401 : ℕ)) ^ (n + 401) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using slowPolynomialSlice_log_cost
      (n + 1) (Fintype.card U) hp hdim hM hMexp (by exact_mod_cast hq) hqexp
  have hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i := by
    intro i
    have hratio : 4 * (q : ℝ) / ρ ≤ Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) :=
      (Real.log_le_iff_le_exp (by positivity)).mp hcost
    simpa only [mul_comm] using (div_le_iff₀ hρ).mp (hratio.trans (hN i))
  obtain ⟨A, hA, hscore, hT⟩ := exists_localMajor_dense_slice_niltest_nine_tenths
    N q hq P E R hP hE htop hR M hM hcoeff f (by
      simpa only [ρ, slowPolynomialSliceRadius, slowPolynomialSliceSlope,
        Nat.cast_add, Nat.cast_one] using hlarge)
  have hA' : IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints := by
    simpa only [ρ, slowPolynomialSliceRadius, slowPolynomialSliceSlope,
      Nat.cast_add, Nat.cast_one] using hA
  exact ⟨A, hA'.mono hcost, hscore, hT⟩

end Erdos3

end

end OAI
