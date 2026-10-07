import OAI.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
import OAI.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds

namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

noncomputable def factorizationInputOffset (s : ℕ) : ℕ :=
  ⌈budget s⌉₊ + 2

theorem budget_le_factorizationInputOffset (s : ℕ) :
    budget s ≤ (factorizationInputOffset s : ℝ) := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast (Nat.le_add_right ⌈budget s⌉₊ 2)

theorem le_factorizationInputBudget (s : ℕ) {p : ℝ} (_hp : 0 ≤ p) :
    p ≤ p + factorizationInputOffset s :=
  le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem factorizationInputBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ p + factorizationInputOffset s :=
  hp.trans (le_factorizationInputBudget s hp)

theorem budget_le_factorizationInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    budget s ≤ p + factorizationInputOffset s :=
  (budget_le_factorizationInputOffset s).trans (le_add_of_nonneg_left hp)

theorem factorizationInputBudget_le_power (s c : ℕ) (hc : 2 ≤ c)
    {p : ℝ} (hp : 0 ≤ p) :
    p + factorizationInputOffset s ≤ (p + factorizationInputOffset s + c) ^ c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hbase : 1 ≤ p + factorizationInputOffset s + c := by
    linarith [factorizationInputBudget_nonneg s hp]
  calc
    p + factorizationInputOffset s ≤ p + factorizationInputOffset s + c :=
      le_add_of_nonneg_right (Nat.cast_nonneg _)
    _ = (p + factorizationInputOffset s + c) ^ 1 := (pow_one _).symm
    _ ≤ (p + factorizationInputOffset s + c) ^ c := pow_le_pow_right₀ hbase (by omega)

theorem exists_factorizationBudget (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + factorizationInputOffset s + c) ^ c ≤ (p + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (factorizationInputOffset s) + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

variable {U : Type*}

noncomputable def orbit (s : ℕ) (_hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    (nilmanifold s).filtration.realification.PolynomialOrbit (fun _ : U => 1) :=
  translationCoordinatePolynomialOrbit weight s weight_pos (weight_le s)
    (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)
    (rename Sum.inl P)
    (majorParameterRename_degree (fun _ : U => 1) weight
      ((mem_weightedSupportLE_one_iff P s).mpr hP))

theorem orbit_realEval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (u : U → ℝ) :
    bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (orbit s hs P hP)) = ⟨0, C (eval u P)⟩ := by
  have hslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u ∈
        weightedSupportLT weight s := by
    intro u α _
    have hα : α = 0 := Subsingleton.elim _ _
    change Finsupp.weight weight α < s
    simpa only [hα, map_zero] using hs
  change bchRealTranslationHom weight s (weight_le s)
    ((weightedFiltration weight s (weight_le s)).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u _) = _
  rw [orbit, translationCoordinatePolynomialOrbit_realEval _ _ _ _ _ _ _ _ hslot,
    specialize_rename]
  rfl

theorem orbit_integerEval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (x : U → ℤ) :
    bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitEval
        (fun _ : U => 1) x (orbit s hs P hP)) =
      ⟨0, C (eval (fun i => (x i : ℝ)) P)⟩ := by
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer, orbit_realEval]

theorem orbit_buffered_eval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (u : U → ℝ) :
    bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
      (bchRealTranslationHom weight s (weight_le s)
        ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
          (fun _ : U => 1) u (orbit s hs P hP))) =
      (Real.fourierChar (eval u P) : ℂ) := by
  rw [orbit_realEval]
  rw [bufferedTranslationPhase_eq_chart (localTentKernel 0 8 (by decide)) 0 _ 0
    (fun i => Fin.elim0 i)]
  have hd : ∀ x y : Fin 0 → ℝ, dist x y = 0 := by
    intro x y
    rw [Subsingleton.elim x y, dist_self]
  simp [bufferedTranslationTerm, translationPhaseArgument, localTentKernel, hd]

private theorem zero_base_orbit (s : ℕ) :
    translationBasePolynomialOrbit weight s weight_pos (weight_le s)
      (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i) = 1 := by
  let := phaseBasisFintype s
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationBasePolynomialOrbit weight s weight_pos (weight_le s)
    (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)).log = 0
  rw [translationBasePolynomialOrbit_log]
  apply VectorPolynomial.coefficients.injective
  ext α
  rw [VectorPolynomial.coefficients_ofCoordinates]
  simp [translationBaseCoordinatePolynomial]

theorem orbit_eq_pure (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    orbit s hs P hP = translationPurePolynomialOrbit weight s weight_pos (weight_le s)
      (rename Sum.inl P)
      (majorParameterRename_degree (fun _ : U => 1) weight
        ((mem_weightedSupportLE_one_iff P s).mpr hP)) := by
  rw [orbit, translationCoordinatePolynomialOrbit, zero_base_orbit, one_mul]

theorem orbit_log (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    letI := phaseBasisFintype s
    (orbit s hs P hP).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis weight s weight_pos).baseChange ℝ)
        (translationPolynomialCoordinatePolynomial weight s (rename Sum.inl P)) := by
  rw [orbit_eq_pure]
  rfl

theorem phaseSlotCoefficient_rename (P : MvPolynomial U ℝ) :
    polynomialSlotCoefficient (0 : Fin 0 →₀ ℕ)
      (rename (Sum.inl : U → U ⊕ Fin 0) P) = P := by
  ext α
  rw [polynomialSlotCoefficient_coeff, Finsupp.sumElim_eq_add]
  simp only [Finsupp.mapDomain_zero, add_zero]
  exact coeff_rename_mapDomain _ Sum.inl_injective P α

theorem orbit_coordinate (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
    (i : WeightedBasisIndex weight s) :
    VectorPolynomial.coordinate
      (((weightedBasis weight s weight_pos).baseChange ℝ).coord i).toAddMonoidHom
      (orbit s hs P hP).log = P := by
  let := phaseBasisFintype s
  rw [orbit_log, VectorPolynomial.coordinate_ofCoordinates]
  cases i with
  | inl i => exact Fin.elim0 i
  | inr α =>
      change polynomialSlotCoefficient α.val (rename Sum.inl P) = P
      rw [Subsingleton.elim α.val 0, phaseSlotCoefficient_rename]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardDetectorOffset (depth : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (depth + 1), OrdinaryPolynomialPhase.factorizationInputOffset r

noncomputable def preparedFiniteForwardDetectorPolynomial (depth : ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (preparedFiniteForwardDetectorOffset depth)

theorem preparedFiniteForwardDetectorOffset_phase (depth r : ℕ) (hr : r ≤ depth) :
    OrdinaryPolynomialPhase.budget r ≤ (preparedFiniteForwardDetectorOffset depth : ℝ) := by
  apply (OrdinaryPolynomialPhase.budget_le_factorizationInputOffset r).trans
  exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (show r ∈ Finset.range (depth + 1) by simpa using Nat.lt_succ_of_le hr) :
    OrdinaryPolynomialPhase.factorizationInputOffset r ≤ preparedFiniteForwardDetectorOffset depth)

@[simp] theorem preparedFiniteForwardDetectorPolynomial_eval (depth : ℕ) (p : ℝ) :
    (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ) p =
      p + preparedFiniteForwardDetectorOffset depth := by
  simp [preparedFiniteForwardDetectorPolynomial]

theorem preparedFiniteForwardDetectorPolynomial_bounds (depth : ℕ)
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    p ≤ (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog u p) ∧
    ∀ r ≤ depth, OrdinaryPolynomialPhase.budget r ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog u p) := by
  rw [preparedFiniteForwardDetectorPolynomial_eval]
  have hc : 0 ≤ (preparedFiniteForwardDetectorOffset depth : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ allocatedModelTestLog u p := by
    unfold allocatedModelTestLog
    positivity
  constructor
  · unfold allocatedModelTestLog
    linarith only [hu, hp, hc]
  · intro r hr
    exact (preparedFiniteForwardDetectorOffset_phase depth r hr).trans
      (le_add_of_nonneg_left hlog)

theorem preparedFiniteForwardDetectorPolynomial_stage_bounds
    (depth A Cdirect : ℕ) (constants : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardWork A constants n x ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision A Cdirect constants n isDirect x gainLog stageLog)
          (preparedFiniteForwardWork A constants n x)) ∧
    ∀ r ≤ depth, OrdinaryPolynomialPhase.budget r ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision A Cdirect constants n isDirect x gainLog stageLog)
          (preparedFiniteForwardWork A constants n x)) :=
  preparedFiniteForwardDetectorPolynomial_bounds depth
    (preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect constants n isDirect hx hg hs)
    (preparedFiniteForwardWork_nonneg A constants n hx)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

theorem phasePair_finrank_le_of_geometry
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {s t e : ℕ}
    (D : RationalFilteredNilmanifold L t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ budget s + p := by
  let : FiniteDimensional ℚ (weightedSubalgebra weight s) :=
    (nilmanifold s).basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : ∀ i : Bool, Module.Finite ℚ (BoolLieFamily (weightedSubalgebra weight s) L i) := by
    intro i
    cases i
    · exact (inferInstance : Module.Finite ℚ L)
    · exact (inferInstance : Module.Finite ℚ (weightedSubalgebra weight s))
  have hphase : (finrank ℚ (weightedSubalgebra weight s) : ℝ) ≤ budget s := by
    rw [Module.finrank_eq_card_basis (nilmanifold s).basis, Fintype.card_fin]
    exact (nilmanifold_geometry s).1
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    rw [Module.finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hpair : finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) =
      finrank ℚ (weightedSubalgebra weight s) + finrank ℚ L := by
    change finrank ℚ (∀ i : Bool, BoolLieFamily (weightedSubalgebra weight s) L i) = _
    rw [Module.finrank_pi_fintype, Fintype.sum_bool]
    rfl
  rw [hpair, Nat.cast_add]
  exact add_le_add hphase hdim

theorem phasePair_finrank_le
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {s t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L t e) {U : Type*} {ω : U → ℕ}
    (R : D.Niltest ω) {p : ℝ} (hR : R.ComplexityLE p) :
    (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ budget s + p :=
  phasePair_finrank_le_of_geometry D hR.1

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_polynomial_phase_factorization (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (hts : t < s)
      (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) * R.eval x‖ →
      let N := pi (pairModels (nilmanifold s) (D.raiseStep hts.le))
      ∃ (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L)))
          ℚ (PairAlgebra (weightedSubalgebra weight s) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement weight s hs 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((nilmanifold s).basis i)) ≤ (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ (p + C) ^ C ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (nilmanifold s) (D.raiseStep hts.le)
            (orbit s hs P hP) (D.raiseStepRealOrbit hts.le R.orbit) b ω hLayers)
          ((p + C) ^ C) := by
  obtain ⟨c, hc, hstep⟩ := exists_translation_major_correlation_step_drop s hs
  obtain ⟨C, hC, hbudget⟩ := exists_factorizationBudget s c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ _ _ _ _ D hts P hP R p hp hR hRcap
    origin lengths hlengths hU hlarge hcorr
  let := phaseBasisFintype s
  dsimp only
  let q : ℝ := p + factorizationInputOffset s
  have hpq : p ≤ q := le_factorizationInputBudget s hp
  have hq : 0 ≤ q := hp.trans hpq
  have hfixed : budget s ≤ q := budget_le_factorizationInputBudget s hp
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := hbudget p hp
  have hgeometry : (nilmanifold s).GeometryComplexityLE q :=
    GeometryComplexityLE.mono _ (nilmanifold_geometry s) hfixed
  have hlog : Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)) ≤ q :=
    (le_max_right _ _).trans hfixed
  have hdetector (x : U → ℤ) :
      bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
        (bchRealTranslationHom weight s (weight_le s)
          ((nilmanifold s).filtration.realification.polynomialOrbitEval (fun _ : U => 1)
            x (orbit s hs P hP))) = (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) := by
    rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
    exact orbit_buffered_eval s hs P hP (fun i => (x i : ℝ))
  have hcorrelation : Real.exp (-q) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
          (bchRealTranslationHom weight s (weight_le s)
            ((nilmanifold s).filtration.realification.polynomialOrbitEval (fun _ : U => 1)
              x (orbit s hs P hP))) * R.eval x‖ := by
    simp_rw [hdetector]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  obtain ⟨η, b, ω, hLayers, hη, hηheight, hbheight, hfactor⟩ :=
    hstep weight weight_pos (weight_le s) D hts (localTentKernel 0 8 (by decide)) 0 0
      (by simp) (by simp [realPolynomialMass]) (orbit s hs P hP)
      R q hq hgeometry hlog (hR.mono hpq) hRcap origin lengths hlengths (hU.trans hpq)
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hlarge i)) hcorrelation
  have hdim : (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤
      (p + C) ^ C := by
    apply (phasePair_finrank_le (s := s) D R hR).trans
    apply le_trans (b := q)
    · dsimp [q]
      linarith [budget_le_factorizationInputOffset s]
    · exact (factorizationInputBudget_le_power s c hc hp).trans hcost
  refine ⟨η, b, ω, hLayers, hη, fun i => (hηheight i).trans hcost,
    fun i j => (hbheight i j).trans hcost, hdim, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hLayers
    hfactor hcost (fun i => by exact_mod_cast hlengths i)

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem orbit_symbol_constantCoefficient {U : Type*} (s : ℕ) (hs : 0 < s)
    (G : NilpotentLieFiltration (weightedSubalgebra weight s) s)
    (hG : ∀ j, G.layer j = Submodule.span ℚ
      (weightedBasis weight s weight_pos '' {i | j ≤ weightedBasisGrade weight s i}))
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
      (G.realSymbolRepresentative
        (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
        hG (fun _ : U => 1)
        (G.realSymbolOfPolynomial
          (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
          hG (fun _ : U => 1)
          (orbit s hs P hP).log)) = homogeneousComponent s P := by
  let := phaseBasisFintype s
  rw [orbit_log, NilpotentLieFiltration.realSymbolRepresentative_ofCoordinates,
    constantCoefficient_coordinate_ofCoordinates s hs]
  have hcoord := orbit_coordinate s hs P hP (constantBasisIndex s hs)
  rw [orbit_log, coordinate_ofCoordinates] at hcoord
  rw [hcoord, constantBasisIndex_grade]
  rfl

theorem pairOrbitSymbol_scalar_top {U ι L : Type} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (hs : 0 < s) {e : ℕ} (D : RationalFilteredNilmanifold L s e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra weight s) L)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels (nilmanifold s) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    (pi (pairModels (nilmanifold s) D)).filtration.scalarSymbolPolynomial b ω hF
      (fun _ : U => 1)
      ((constantCoefficient s).comp
        (gradedProjection (pi (pairModels (nilmanifold s) D)).filtration
          (liePiEval (R := ℚ)
            (M := BoolLieFamily (weightedSubalgebra weight s) L) true)).toLinearMap)
      (pairOrbitSymbol (nilmanifold s) D (orbit s hs P hP) q b ω hF) =
        homogeneousComponent s P := by
  let N := pi (pairModels (nilmanifold s) D)
  let c := weightedBasis weight s weight_pos
  let ν := weightedBasisGrade weight s
  have hG : ∀ j, (weightedFiltration weight s (weight_le s)).layer j =
      Submodule.span ℚ (c '' {i | j ≤ ν i}) :=
    weightedFiltration_layer_eq_span weight s weight_pos (weight_le s)
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  have hfirst := pairOrbitSymbol_first_projection (nilmanifold s) D (fun _ : U => 1)
    b ω hF c ν hG (orbit s hs P hP) q
  have hphase : coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
      ((weightedFiltration weight s (weight_le s)).realSymbolRepresentative c ν hG (fun _ : U => 1)
        ((weightedFiltration weight s (weight_le s)).realSymbolOfPolynomial c ν hG (fun _ : U => 1)
          (orbit s hs P hP).log)) = homogeneousComponent s P := by
    have hh := orbit_symbol_constantCoefficient s hs (weightedFiltration weight s (weight_le s)) hG P hP
    simpa only [c, ν] using hh
  have hresult := N.filtration.homogeneousProjected_scalar_identity
    (weightedFiltration weight s (weight_le s)) b ω hF c ν hG
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ
    (projection_filtered N.filtration φ) (fun _ : U => 1)
    (constantCoefficient s)
    (pairOrbitSymbol (nilmanifold s) D (orbit s hs P hP) q b ω hF).coord
    ((weightedFiltration weight s (weight_le s)).realSymbolOfPolynomial c ν hG (fun _ : U => 1)
      (orbit s hs P hP).log) (homogeneousComponent s P) hfirst hphase
  simpa only [N, c, ν, φ,
    NilpotentLieFiltration.scalarSymbolPolynomial, gradedProjection] using hresult

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_ordinary_polynomial_phase_inverse (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (_hts : t < s)
      (P : MvPolynomial U ℝ) (_hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) * R.eval x‖ →
      PolynomialRationalApproximation (fun i => (lengths i : ℝ))
        (Real.exp ((p + C) ^ C)) (homogeneousComponent s P) := by
  obtain ⟨a, _ha, hfactorization⟩ := exists_polynomial_phase_factorization s hs
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ D hts P hP R p hp hR hRcap
    origin lengths hlengths hU hlarge hcorr
  let : FiniteDimensional ℚ (weightedSubalgebra weight s) :=
    (nilmanifold s).basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
    realification_moduleTopology_t2 (nilmanifold s).basis
  let q : ℝ := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfirst : q ≤ (p + C) ^ C := by nlinarith [show 0 ≤ (q + 3) ^ 3 by positivity]
  have hlast : (q + 3) ^ 3 ≤ (p + C) ^ C := by linarith
  obtain ⟨η, b, ω, hF, hη, _hηheight, hb, hdim, hfactor⟩ :=
    hfactorization D hts P hP R p hp hR hRcap origin lengths hlengths hU
      (fun i => (Real.exp_le_exp.mpr hfirst).trans (hlarge i)) hcorr
  let N := pi (pairModels (nilmanifold s) (D.raiseStep hts.le))
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  let X := pairOrbitSymbol (nilmanifold s) (D.raiseStep hts.le)
    (orbit s hs P hP) (D.raiseStepRealOrbit hts.le R.orbit) b ω hF
  have hT : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional N.filtration φ
        (N.filtration.associatedGradedBasis b ω hF i)) ≤ q :=
    pairScalarFunctional_basis_logHeight s hs (D.raiseStep hts.le) b ω hF hq hb
  have hfactor' : N.filtration.ControlledSymbolFactorization b ω hF
      (η.comp φ.toLinearMap) (fun i => (lengths i : ℝ)) X q := by
    rw [← pairFrequency_zero_comp]
    exact hfactor
  have happ := controlledFactorization_approximation_of_normalized_frequency
    N.filtration b ω hF φ hs η hη (fun i => (lengths i : ℝ)) hT X q hq
    (by simpa only [Fintype.card_fin] using hdim) hθ hfactor'
  have htop : N.filtration.scalarSymbolPolynomial b ω hF (fun _ : U => 1)
      (projectedScalarFunctional N.filtration φ) X = homogeneousComponent s P :=
    pairOrbitSymbol_scalar_top s hs (D.raiseStep hts.le) b ω hF P hP
      (D.raiseStepRealOrbit hts.le R.orbit)
  rw [htop] at happ
  exact happ.mono (Real.exp_le_exp.mpr hlast) hT

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_ordinary_polynomial_phase_affine_inverse (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (_hts : t < s)
      (P : MvPolynomial U ℝ) (_hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (r : U → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : U → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * x i : ℤ) : ℝ)) P) : ℂ) *
          R.eval x‖ →
      PolynomialRationalApproximation N (Real.exp ((p + C) ^ C))
        (homogeneousComponent s P) := by
  obtain ⟨a, _, hinverse⟩ := exists_ordinary_polynomial_phase_inverse s hs
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.C s * Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ D hts P hP R p hp hR hRcap
    q hq hqp r K hK hKp N hN origin lengths hlengths hNL hdim hlarge hcorr
  let b : ℝ := (p + a) ^ a
  have hcost : b + (s : ℝ) * p ≤ (p + C) ^ C := by
    simpa [Q, b, Polynomial.eval₂_pow] using hbudget p hp
  have hfirst : b ≤ (p + C) ^ C := by
    exact (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hp)).trans hcost
  let P' := residueAffinePolynomial q r P
  have hP' : P'.totalDegree ≤ s := residueAffinePolynomial_totalDegree_le q r P s hP
  have hcorr' : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
      (Real.fourierChar (eval (fun i => (x i : ℝ)) P') : ℂ) * R.eval x‖ := by
    simpa only [P', residueAffinePolynomial_eval] using hcorr
  have happ : PolynomialRationalApproximation (fun i => (lengths i : ℝ))
      (Real.exp b) (homogeneousComponent s P') :=
    hinverse D hts P' hP' R p hp hR hRcap origin lengths hlengths hdim
      (fun i => (Real.exp_le_exp.mpr hfirst).trans (hlarge i)) hcorr'
  have hbound {z : ℝ} (hz : 0 ≤ z) (hzp : z ≤ Real.exp p) :
      z ^ s * Real.exp b ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ (Real.exp p) ^ s * Real.exp b :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz hzp s) (Real.exp_nonneg b)
      _ = Real.exp (b + (s : ℝ) * p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  exact happ.affine_pullback N (fun i => (lengths i : ℝ)) hN
    (fun i => by exact_mod_cast hlengths i) q s hq r K hK hNL
    (Real.exp b) (Real.exp ((p + C) ^ C))
    (hbound (Nat.cast_nonneg q) hqp) (hbound (by linarith) hKp) P hP

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
