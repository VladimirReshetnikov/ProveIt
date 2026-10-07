import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorCorrelationBudget
import OAI.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
import OAI.Combinatorics.Progressions.Estimates.ReducedTranslationMajorTwistedVerticalSelection

namespace OAI

universe u

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_vertical_selection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [LieRing L] [LieAlgebra ℚ L]
      {m d t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d) (ω : U → ℕ)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ M)
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit ω)
      (R : D.Niltest ω) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω (sample x) orbit)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationNilmanifold w d hw hwd).Niltest ω)
        (W : (D.raiseStep htd.le).Niltest ω),
        V.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        V.orbit = orbit ∧ V.normBound = 1 ∧
        W.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (raisedNiltestBudget p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((raisedNiltestBudget p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ m d t e w hw hd hwd _ _ _ _ _ _ _ _ _ D htd ω Ψ D₀ M hdegree hD
    orbit R p hp hgeometry hbound hR hRcap B hB sample multiplier hmultiplier hcorr
  let Q := weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD orbit
  have hQ : Q.ComplexityLE p :=
    weightedTranslationBufferedNiltest_complexity w d hw hwd ω hd Ψ D₀ M hdegree hD orbit
      hgeometry hbound
  have hraise := le_raisedNiltestBudget p
  have hraisedcorr : Real.exp (-(raisedNiltestBudget p)) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hraise)).trans
    simpa only [Q, weightedTranslationBufferedNiltest_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hcorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget p) (hp.trans hraise)
      (hQ.mono hraise) (R.raiseStep_complexity htd.le hp hR)
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_selected_frequency_one w d hw hd hwd Ψ D₀ η V.observable
      hvertV hVne hpresV
  exact ⟨η, V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne, hbias⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

abbrev PairAlgebra (L M : Type u) := ∀ i : Bool, BoolLieFamily L M i

def pairModels (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e) :
    ∀ i : Bool, RationalFilteredNilmanifold (BoolLieFamily L M i) s (Bool.rec e d i)
  | false => E
  | true => D

def pairFrequencies (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) :
    ∀ i : Bool, BoolLieFamily L M i →ₗ[ℚ] ℚ
  | false => θ
  | true => η

noncomputable def pairFrequency (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) :
    PairAlgebra L M →ₗ[ℚ] ℚ := piFrequency (pairFrequencies η θ)

@[simp] theorem pairFrequency_apply (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ)
    (x : PairAlgebra L M) : pairFrequency η θ x = η (x true) + θ (x false) := by
  rw [pairFrequency, piFrequency_apply, Fintype.sum_bool]
  rfl

variable (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    {σ ι : Type*} {w : σ → ℕ}

noncomputable def pairOrbit (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    (pi (pairModels D E)).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.piRealOrbit (fun i => (pairModels D E i).filtration)
    (fun i => by cases i; exact q; exact p)

noncomputable def pairOrbitSymbol (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pi (pairModels D E)).filtration.RealPolynomialSymbolGroup w :=
  (pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF w
    ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

noncomputable def pairTests (V : D.Niltest w) (W : E.Niltest w) :
    ∀ i : Bool, (pairModels D E i).Niltest w
  | false => W
  | true => V

theorem pairTests_complexity (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    ∀ i, (pairTests D E V W i).ComplexityLE p := by
  intro i
  cases i
  · exact hW
  · exact hV

section ProductTopology

variable [TopologicalSpace (ℝ ⊗[ℚ] PairAlgebra L M)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PairAlgebra L M)]
    [T2Space (ℝ ⊗[ℚ] PairAlgebra L M)]

noncomputable def pairNiltest (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pi (pairModels D E)).Niltest w :=
  piNiltest (pairModels D E) (pairTests D E V W) (by linarith)
    (by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp)
    (pairTests_complexity D E V W hV hW)

theorem pairNiltest_eval (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) (x : σ → ℤ) :
    (pairNiltest D E V W hp hV hW).eval x = V.eval x * W.eval x := by
  rw [pairNiltest, piNiltest_eval, Fintype.prod_bool]
  rfl

theorem pairNiltest_complexity (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pairNiltest D E V W hp hV hW).ComplexityLE (productNiltestBudget p) :=
  piNiltest_complexity (pairModels D E) (pairTests D E V W) (by linarith)
    (by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp)
    (pairTests_complexity D E V W hV hW)

@[simp] theorem pairNiltest_orbit (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pairNiltest D E V W hp hV hW).orbit = pairOrbit D E V.orbit W.orbit := rfl

@[simp] theorem pairNiltest_symbol (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pairNiltest D E V W hp hV hW).symbol b ω hF =
      pairOrbitSymbol D E V.orbit W.orbit b ω hF := rfl

theorem pairNiltest_orbit_eq (V V' : D.Niltest w) (W W' : E.Niltest w)
    {p q : ℝ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hV : V.ComplexityLE p) (hW : W.ComplexityLE p)
    (hV' : V'.ComplexityLE q) (hW' : W'.ComplexityLE q)
    (hVo : V.orbit = V'.orbit) (hWo : W.orbit = W'.orbit) :
    (pairNiltest D E V W hp hV hW).orbit =
      (pairNiltest D E V' W' hq hV' hW').orbit := by
  rw [pairNiltest_orbit, pairNiltest_orbit, hVo, hWo]

theorem pairNiltest_symbol_eq_of_orbit_eq (V V' : D.Niltest w) (W W' : E.Niltest w)
    {p q : ℝ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hV : V.ComplexityLE p) (hW : W.ComplexityLE p)
    (hV' : V'.ComplexityLE q) (hW' : W'.ComplexityLE q)
    (hVo : V.orbit = V'.orbit) (hWo : W.orbit = W'.orbit)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pairNiltest D E V W hp hV hW).symbol b ω hF =
      (pairNiltest D E V' W' hq hV' hW').symbol b ω hF := by
  rw [pairNiltest_symbol, pairNiltest_symbol, hVo, hWo]

end ProductTopology
end RationalFilteredNilmanifold

open RationalFilteredNilmanifold

theorem exists_native_pair_vertical_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p : ℝ} (_hp : 2 ≤ p) (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ),
          (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            V.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) →
          (∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
            W.observable (z • x) = CircleFourier.character
              ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, V.eval x * W.eval x‖ →
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun i => (lengths i : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_finite_product_vertical_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
  let models := pairModels D E
  let tests := pairTests D E V W
  let : FiniteDimensional ℚ (PairAlgebra L M) :=
    (productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra L M)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra L M) :=
    realification_moduleTopology_t2 (productFinBasis models)
  have hp0 : 0 ≤ p := by linarith
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  have htests : ∀ i, (tests i).ComplexityLE p := pairTests_complexity D E V W hV hW
  obtain ⟨b, ω, hF, hb, hconstruct⟩ := hstep models tests hp0 hcard htests
  refine ⟨b, ω, hF, hb, ?_⟩
  intro η θ hη hθ origin lengths hlengths hσ hlarge hbias
  have hvert : ∀ i z, z ∈ (models i).filtration.realification.subgroup s → ∀ x,
      (tests i).observable (z • x) = CircleFourier.character
        ((realifyFunctional (pairFrequencies η θ i) z.coord : ℝ) : CircleFourier.Circle) *
          (tests i).observable x := by
    intro i
    cases i
    · exact hθ
    · exact hη
  have hbias' : Real.exp (-p) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths, ∏ i, (tests i).eval x‖ := by
    have heval (x : σ → ℤ) : (∏ i, (tests i).eval x) = V.eval x * W.eval x := by
      rw [Fintype.prod_bool]
      rfl
    simp_rw [heval]
    exact hbias
  exact hconstruct (pairFrequencies η θ) hvert origin lengths hlengths hσ hlarge hbias'

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem pairFrequency_logHeight
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) {p : ℝ}
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθ : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (k : Fin (Fintype.card (Σ i : Bool, Fin (Bool.rec e d i)))) :
    rationalLogHeight (pairFrequency η θ ((pi (pairModels D E)).basis k)) ≤ p := by
  apply piFrequency_logHeight (pairModels D E) (pairFrequencies η θ)
  intro i
  cases i
  · exact hθ
  · exact hη

theorem exists_native_pair_positive_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p : ℝ} (_hp : 2 ≤ p) (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ),
          (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
          (∀ i, rationalLogHeight (θ (E.basis i)) ≤ p) →
          (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            V.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) →
          (∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
            W.observable (z • x) = CircleFourier.character
              ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, V.eval x * W.eval x‖ →
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun i => (lengths i : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF) ((p + C) ^ C) := by
  by_cases hs2 : 2 ≤ s
  · obtain ⟨C, hC, hstep⟩ := exists_native_pair_vertical_step_drop s hs2
    refine ⟨C, hC, ?_⟩
    intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
    obtain ⟨b, ω, hF, hb, hconstruct⟩ := hstep D E V W hp hV hW
    exact ⟨b, ω, hF, hb, fun η θ _ _ => hconstruct η θ⟩
  · have hs1 : s = 1 := by omega
    subst s
    let X : Polynomial ℕ := Polynomial.X
    let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + 2) ^ 4)
    refine ⟨C, hC, ?_⟩
    intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
    let models := pairModels D E
    let N := pi models
    let : FiniteDimensional ℚ (PairAlgebra L M) :=
      (productFinBasis models).finiteDimensional_of_finite
    let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra L M)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M) :=
      IsModuleTopology.isTopologicalAddGroup ℝ _
    let : T2Space (ℝ ⊗[ℚ] PairAlgebra L M) :=
      realification_moduleTopology_t2 (productFinBasis models)
    have hp0 : 0 ≤ p := by linarith
    have hpq : p ≤ productNiltestBudget p := by
      have hr := productObservableLipBudget_nonneg hp0
      unfold productNiltestBudget
      nlinarith [sq_nonneg (p + 2), sq_nonneg p]
    have hq : 0 ≤ productNiltestBudget p := hp0.trans hpq
    have hcost : (productNiltestBudget p + 2) ^ 4 ≤ (p + C) ^ C := by
      simpa [X, Q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
        using hbudget p hp0
    have hnonneg : 0 ≤ (p + C) ^ C := by positivity
    have hdim : finrank ℚ (PairAlgebra L M) =
        Fintype.card (Σ i : Bool, Fin (Bool.rec e d i)) := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis N.basis
    rw [hdim]
    let ω : Fin (Fintype.card (Σ i : Bool, Fin (Bool.rec e d i))) → ℕ := fun _ => 1
    have hF : ∀ k, N.filtration.layer k =
        Submodule.span ℚ (N.basis '' {i | k ≤ ω i}) :=
      N.filtration.stepOne_basis_layers N.basis
    refine ⟨N.basis, ω, hF, ?_, ?_⟩
    · intro i j
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simpa [rationalLogHeight] using hnonneg
    · intro η θ hηheight hθheight hη hθ origin lengths hlengths _hσ _hlarge hbias
      let T := pairNiltest D E V W hp hV hW
      have hT : T.ComplexityLE (productNiltestBudget p) :=
        pairNiltest_complexity D E V W hp hV hW
      have hfreq : ∀ i, rationalLogHeight (pairFrequency η θ (N.basis i)) ≤
          productNiltestBudget p :=
        fun i => (pairFrequency_logHeight D E η θ hηheight hθheight i).trans hpq
      have hvert : ∀ z, z ∈ N.filtration.realification.subgroup 1 → ∀ x,
          T.observable (z • x) = CircleFourier.character
            ((realifyFunctional (pairFrequency η θ) z.coord : ℝ) : CircleFourier.Circle) *
              T.observable x := by
        apply piNiltest_vertical (pairModels D E) (pairTests D E V W)
          (pairFrequencies η θ)
        intro i
        cases i
        · exact hθ
        · exact hη
      have hbias' : Real.exp (-productNiltestBudget p) ≤
          ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ := by
        simp_rw [show ∀ x, T.eval x = V.eval x * W.eval x from
          pairNiltest_eval D E V W hp hV hW]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
      have hf := N.stepOne_controlled_symbol_factorization ω hF T (pairFrequency η θ)
        hq hT hfreq hvert origin lengths hlengths hbias'
      have hf' := NilpotentLieFiltration.ControlledSymbolFactorization.mono
        N.filtration N.basis ω hF hf hcost (fun i => by exact_mod_cast hlengths i)
      exact hf'

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem pairOrbitSymbol_eq_of_right_symbol_eq
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} {σ ι κ : Type*} {w : σ → ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels D E)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hE : ∀ j, E.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (p : D.filtration.realification.PolynomialOrbit w)
    (q q' : E.filtration.realification.PolynomialOrbit w)
    (hq : E.filtration.realPolynomialSymbolHom c ν hE w
        (E.filtration.realification.polynomialOrbitCoordinates w q) =
      E.filtration.realPolynomialSymbolHom c ν hE w
        (E.filtration.realification.polynomialOrbitCoordinates w q')) :
    pairOrbitSymbol D E p q b ω hF = pairOrbitSymbol D E p q' b ω hF := by
  classical
  have hq' : E.filtration.realSymbolOfPolynomial c ν hE w q.log =
      E.filtration.realSymbolOfPolynomial c ν hE w q'.log :=
    congrArg NilpotentLieBCHGroup.coord hq
  have hcoeff := (E.filtration.realification.polynomialSymbolMap_eq_iff w
    ⟨q.log, q.property⟩ ⟨q'.log, q'.property⟩).mp
      ((E.filtration.realSymbolOfPolynomial_eq_iff_symbolMap_eq c ν hE w
        ⟨q.log, q.property⟩ ⟨q'.log, q'.property⟩).mp hq')
  have hlog : (pairOrbit D E p q).log - (pairOrbit D E p q').log =
      VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
        (q.log - q'.log) := by
    simp only [pairOrbit, piRealOrbit, Fintype.sum_bool]
    let f := VectorPolynomial.map (σ := σ)
      ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
    let f₀ := VectorPolynomial.map (σ := σ)
      ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ)
    change f₀ p.log + f q.log - (f₀ p.log + f q'.log) = f (q.log - q'.log)
    calc
      _ = f q.log - f q'.log := by abel
      _ = _ := (map_sub f q.log q'.log).symm
  apply NilpotentLieBCHGroup.ext
  change (pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF w
      (pairOrbit D E p q).log =
    (pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF w
      (pairOrbit D E p q').log
  apply ((pi (pairModels D E)).filtration.realSymbolOfPolynomial_eq_iff_symbolMap_eq
    b ω hF w
    ⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩
    ⟨(pairOrbit D E p q').log, (pairOrbit D E p q').property⟩).mpr
  apply ((pi (pairModels D E)).filtration.realification.polynomialSymbolMap_eq_iff w
    ⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩
    ⟨(pairOrbit D E p q').log, (pairOrbit D E p q').property⟩).mpr
  intro α
  change coefficients ((pairOrbit D E p q).log - (pairOrbit D E p q').log) α ∈ _
  rw [hlog]
  have hmap := VectorPolynomial.coefficients_map
    ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
    (q.log - q'.log) α
  rw [hmap]
  exact realProductSingle_mem_layer (fun i => (pairModels D E i).filtration)
    false _ (hcoeff α)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_correlation_step_drop (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ M)
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x orbit)) * R.eval x‖ →
      let N := pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hF : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d (by omega) 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
            orbit (D.raiseStepRealOrbit htd.le R.orbit) b ω hF) ((p + C) ^ C) := by
  obtain ⟨a, ha, hselect⟩ := exists_translation_major_vertical_selection
  obtain ⟨c, _hc, hstep⟩ := exists_native_pair_positive_step_drop d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorCorrelationBudget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd Ψ D₀ M hdegree hD
    orbit R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  dsimp only
  have hbox : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    exact ⟨le_rfl, by have hi := hlengths i; omega⟩
  obtain ⟨η, V, W, hVc, hVo, _hVn, hWc, hWo, _hWn, hheight, hη, hvertV, hvertW,
      _hVne, _hWne, hbias⟩ :=
    hselect w hw (by omega) hwd D htd (fun _ : U => 1) Ψ D₀ M hdegree hD
      orbit R p hp hgeometry hbound hR hRcap (translatedIntegerBox origin lengths) hbox
      (fun x => x) (fun _ => 1) (fun _ _ => by simp)
      (by simpa only [one_mul] using hcorr)
  let r := translationMajorPairBudget a p
  have hcontrols := translationMajorPairBudget_controls a hp ha
  have hpr : p ≤ r := hcontrols.1.trans hcontrols.2.1
  have hr : 2 ≤ r := hcontrols.2.2
  have hcost := hbudget p hp
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le) V W hr hVc hWc
  have hzeroheight : ∀ i, rationalLogHeight ((0 : L →ₗ[ℚ] ℚ)
      ((D.raiseStep htd.le).basis i)) ≤ r := by
    intro i
    simpa [rationalLogHeight] using (show 0 ≤ r by linarith)
  have hfactor := hconstruct η (0 : L →ₗ[ℚ] ℚ) hheight hzeroheight hvertV hvertW origin lengths hlengths
    (hU.trans hpr) (fun i => (Real.exp_le_exp.mpr hcost.2).trans (hlarge i))
    (by simpa only [one_mul, r, translationMajorPairBudget] using hbias)
  rw [hVo, hWo] at hfactor
  refine ⟨η, b, ω, hF, hη, fun i => (hheight i).trans hcost.1,
    fun i j => (hb i j).trans hcost.2, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hF hfactor hcost.2
    (fun i => by exact_mod_cast hlengths i)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_twisted_correlation_step_drop (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (B K : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ B)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ B K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x orbit)) * R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hF : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le) orbit (D.raiseStepRealOrbit htd.le R.orbit) b ω hF)
          ((p + C) ^ C) := by
  obtain ⟨a, ha, hselect⟩ := exists_translation_major_twisted_vertical_selection
  obtain ⟨c, _hc, hstep⟩ := exists_native_pair_positive_step_drop d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorCorrelationBudget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ D₀ B K hdegree hD
    T hT hLip orbit R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  dsimp only
  have hbox : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    exact ⟨le_rfl, by have hi := hlengths i; omega⟩
  obtain ⟨η, V, W, hVc, hVo, _hVn, hWc, hWo, _hWn, hheight, hη, hvertV, hvertW,
      _hVne, _hWne, hbias⟩ :=
    hselect w hw hd hwd M hM D htd (fun _ : U => 1) Ψ D₀ B K hdegree hD
      T hT hLip orbit R p hp hgeometry hbound hR hRcap
      (translatedIntegerBox origin lengths) hbox
      (fun x => x) (fun _ => 1) (fun _ _ => by simp)
      (by simpa only [one_mul] using hcorr)
  let r := translationMajorPairBudget a p
  have hcontrols := translationMajorPairBudget_controls a hp ha
  have hpr : p ≤ r := hcontrols.1.trans hcontrols.2.1
  have hr : 2 ≤ r := hcontrols.2.2
  have hcost := hbudget p hp
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (weightedTranslationResidueNilmanifold w d hw hwd M hM)
      (D.raiseStep htd.le) V W hr hVc hWc
  have hzero : ∀ i, rationalLogHeight
      ((0 : L →ₗ[ℚ] ℚ) ((D.raiseStep htd.le).basis i)) ≤ r := by
    intro i
    simpa [rationalLogHeight] using (show (0 : ℝ) ≤ r by linarith)
  have hfactor := hconstruct η (0 : L →ₗ[ℚ] ℚ) hheight hzero
    hvertV hvertW origin lengths hlengths (hU.trans hpr)
    (fun i => (Real.exp_le_exp.mpr hcost.2).trans (hlarge i))
    (by simpa only [one_mul, r, translationMajorPairBudget] using hbias)
  rw [hVo, hWo] at hfactor
  refine ⟨η, b, ω, hF, hη, fun i => (hheight i).trans hcost.1,
    fun i j => (hb i j).trans hcost.2, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hF hfactor hcost.2
    (fun i => by exact_mod_cast hlengths i)

end Erdos3.PolynomialTranslationLie

end

end OAI
