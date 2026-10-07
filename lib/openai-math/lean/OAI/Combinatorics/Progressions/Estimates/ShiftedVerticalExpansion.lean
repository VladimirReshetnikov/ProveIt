/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Nilpotent.BoxNiltestDetection
import OAI.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest
import OAI.Combinatorics.Progressions.Nilpotent.PolarizedVerticalNiltest

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p → ∀ (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      ∀ h : σ → ℤ, ∃ (n : ℕ)
        (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n)
        (S : Q.Niltest w),
        S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x : σ → ℤ, S.eval x = T.eval (fun i => x i + h i) * star (T.eval x) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT χ hvert h
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw h T.orbit
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, hSB, hS, hSval⟩ :=
    D.exists_square_niltest_with_budget T hp hT a b c hrec ε q χ hvert A hA (hALip ε hε)
  refine ⟨_, _, S, hSB, hS.mono (hbudget p hp), ?_⟩
  intro x
  exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
    (D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) T.orbit)
    (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
    (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_uniform_two_shift_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∃ (n : ℕ) (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n),
        Q.GeometryComplexityLE (squareGeometryBudget p) ∧
        ∀ (χ : D.RealGroup → CircleFourier.Circle),
          (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
            T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ a b : σ → ℤ, ∃ S : Q.Niltest w,
          S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
          ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b)) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  refine ⟨_, _, hgeom, ?_⟩
  intro χ hvert h k
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw (h - k) T.orbit
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨S, _, _, hSB, hS, hSval⟩ := hconstruct ε q χ hvert A hA (hALip ε hε)
  have hval (x : σ → ℤ) : S.eval x = T.eval (x + (h - k)) * star (T.eval x) := by
    exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
      (D.filtration.realification.polynomialOrbitEval w (fun i => x i + (h - k) i) T.orbit)
      (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
      (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)
  refine ⟨S.translate hw k, hSB, hS.mono (hbudget p hp), ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_translate, hval]
  congr 2
  abel

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

universe u v

theorem exists_vertical_derivative_detection (s : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ c : ℕ,
      BoxNiltestDetection.{u,v} s (fun q => (q + c) ^ c) →
      ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u}
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (p q : ℝ),
      0 ≤ p → 0 ≤ q → (Fintype.card σ : ℝ) ≤ q → (p + b) ^ b ≤ q →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) → ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∀ (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      ∀ (h a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
      (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
      Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f (multiplicativeDerivative T.eval h)‖ →
      Real.exp (-((q + c) ^ c)) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f := by
  obtain ⟨b, hb, hsq⟩ := exists_controlled_normalized_square s
  refine ⟨b, hb, ?_⟩
  intro c hI σ _ _ L _ _ d _ _ _ _ D p q hp hq hσ hcost w hw T hT χ hvert h a lengths _ f hf hc
  let K := D.filtration.squareLieSubalgebra
  let M := K ⧸ D.filtration.squareFiltration.layerIdeal (s + 1)
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ K := inferInstance
  let : FiniteDimensional ℚ M := inferInstance
  let : TopologicalSpace (ℝ ⊗[ℚ] K) := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] K) := inferInstance
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 (Module.finBasis ℚ K)
  let : TopologicalSpace (ℝ ⊗[ℚ] M) := moduleTopology ℝ (ℝ ⊗[ℚ] M)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M) := IsModuleTopology.topologicalAddGroup ℝ _
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] M) := inferInstance
  let : T2Space (ℝ ⊗[ℚ] M) := realification_moduleTopology_t2 (Module.finBasis ℚ M)
  obtain ⟨n, E, S, _, hS, hval⟩ := hsq D p hp w hw T hT χ hvert h
  have heval : S.conjugate.eval = multiplicativeDerivative T.eval h := by
    funext x
    rw [RationalFilteredNilmanifold.Niltest.eval_conjugate, hval]
    simp only [multiplicativeDerivative, star_mul, star_star]
    rfl
  have hc' : Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f S.conjugate.eval‖ := by
    rwa [heval]
  exact hI E q hq hσ w hw S.conjugate (hS.mono hcost) a lengths f hf hc'

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_shifted_product_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      {p : ℝ} (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → D.GeometryComplexityLE p → (∀ k, 0 < w k) → ∀ (i j : I) (a b : σ → ℤ),
      ∃ (n : Fin 4 → ℕ)
        (Q : ∀ k, RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s (n k))
        (S : ∀ k, (Q k).Niltest w),
        (∀ k, (S k).normBound = 4) ∧ (∀ k, (S k).ComplexityLE ((p + C) ^ C)) ∧
        ∀ x, V.observable i (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w (x + a) g)) *
          star (V.observable j (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w (x + b) g))) =
          ∑ k, polarizationWeight k * (S k).eval x := by
  obtain ⟨A, _, hsquare⟩ := exists_uniform_two_shift_square s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + 5 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D _ _ _ _ _ _ _ _ p V w g hp hD hw i j a b
  have hbound : (p + 5 + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  let T : Fin 4 → D.Niltest w := fun k =>
    V.combinationNiltest g i j (polarizationPhase k) (polarizationPhase_norm k).le
  have hparts : ∀ k, ∃ (n : ℕ)
      (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)) s n) (S : Q.Niltest w),
      S.normBound = 4 ∧ S.ComplexityLE ((p + C) ^ C) ∧
      ∀ x, S.eval x = (T k).eval (x + a) * star ((T k).eval (x + b)) := by
    intro k
    obtain ⟨n, Q, _, hconstruct⟩ := hsquare D (p + 5) (by linarith) w hw (T k)
      (V.combinationNiltest_complexity g i j _ _ hp hD)
    obtain ⟨S, hSn, hSc, hSe⟩ := hconstruct
      (fun z => ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle))
      (fun z hz x => V.coordinateCombination_vertical i j (polarizationPhase k) z hz x) a b
    refine ⟨n, Q, S, ?_, hSc.mono hbound, hSe⟩
    calc
      S.normBound = (T k).normBound ^ 2 := hSn
      _ = 4 := by norm_num [T, combinationNiltest]
  choose n Q S hSn hSc hSe using hparts
  refine ⟨n, Q, S, hSn, hSc, ?_⟩
  intro x
  refine (complex_mixed_polarization _
    (V.observable j (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (x + a) g)))
    (V.observable i (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (x + b) g))) _).trans ?_
  apply Finset.sum_congr rfl
  intro k _
  rw [hSe k x]
  rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
