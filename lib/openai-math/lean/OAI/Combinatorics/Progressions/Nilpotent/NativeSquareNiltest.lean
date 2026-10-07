import OAI.Combinatorics.Progressions.Estimates.NativeSquareOrbit
import OAI.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
import OAI.Combinatorics.Progressions.Estimates.SpecifiedSquareObservable

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_square_quotient_niltest_with_orbit
    (b : Basis (Fin m) ℚ F.squareLieSubalgebra) (v : Fin m → ℕ)
    (hlayers : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (F.squareLattice Γ))
    (hout : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid N)
    (w : σ → ℕ) (q : F.squareFiltration.realification.PolynomialOrbit w)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) N hN hout
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
    ∀ H : ℕ, 1 ≤ H →
      (∀ i j, RationalHeightLE (D.basis.repr
        (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H) →
      (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
    ∃ T : D.Niltest w,
      T.orbit = F.squareFiltration.realQuotientPolynomialOrbit
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
      (∀ z : F.squareFiltration.realification.Group,
        T.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
          F.realSquareObservable Γ ε u (QuotientGroup.mk z)) ∧
      T.normBound = B ^ 2 ∧
      T.lipBound = rationalReconstructionLipschitzBound s m
        (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2) ∧
      ∀ x : σ → ℤ, T.eval x = F.realSquareObservable Γ ε u
        (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  dsimp only
  intro H hH he hc
  let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
  obtain ⟨f, hf, hfLip, hfBound⟩ := F.exists_lipschitz_realSquare_descent Γ
    b D.basis N N H hN hN hH hout D.outer_grid he hc ε u χ hu A B hLip hb
  let K := rationalReconstructionLipschitzBound s m
    (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2)
  let T : D.Niltest w := {
    orbit := F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q
    observable := f
    normBound := B ^ 2
    lipBound := K
    norm_le := fun x => by simpa only [NNReal.coe_pow] using hfBound x
    lipschitz := by
      let : MetricSpace (F.squareFiltration.quotientTop.realification.Group ⧸
          ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
            (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :=
        realificationQuotientMetricSpace D.basis _ N hN D.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin, K]; exact le_rfl) }
  refine ⟨T, rfl, hf, rfl, rfl, ?_⟩
  intro x
  change f (QuotientGroup.mk ((F.squareFiltration.quotientTop.realification.polynomialOrbitEval w x)
    (F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q))) = _
  exact (congrArg (fun g : F.squareFiltration.quotientTop.realification.Group =>
      f (QuotientGroup.mk g))
    (F.squareFiltration.realQuotientPolynomialOrbit_eval
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q x)).trans (hf _)

theorem exists_square_quotient_niltest
    (b : Basis (Fin m) ℚ F.squareLieSubalgebra) (v : Fin m → ℕ)
    (hlayers : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (F.squareLattice Γ))
    (hout : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid N)
    (w : σ → ℕ) (q : F.squareFiltration.realification.PolynomialOrbit w)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) N hN hout
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
    ∀ H : ℕ, 1 ≤ H →
      (∀ i j, RationalHeightLE (D.basis.repr
        (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H) →
      (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
    ∃ T : D.Niltest w,
      T.normBound = B ^ 2 ∧
      T.lipBound = rationalReconstructionLipschitzBound s m
        (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2) ∧
      ∀ x : σ → ℤ, T.eval x = F.realSquareObservable Γ ε u
        (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  dsimp only
  intro H hH he hc
  obtain ⟨T, _, _, hT⟩ := F.exists_square_quotient_niltest_with_orbit Γ b v hlayers N hN hin hout
    w q ε u χ hu A B hLip hb H hH he hc
  exact ⟨T, hT⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

theorem exists_uniform_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c)) :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout
      Q.GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
        (χ : D.RealGroup → CircleFourier.Circle),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ (A : ℝ≥0), (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) →
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) →
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeom, hgeomQ⟩ :=
    D.exists_controlled_reduced_square_geometry hp hT.1
  let m := Fintype.card (Fin (finrank ℚ L) ⊕ {i // 2 ≤ v₀ i})
  let bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra := D.filtration.squareFinBasis b₀ v₀ (hlayers 2)
  let v : Fin m → ℕ := squareFinWeight v₀
  have hls := D.filtration.squareFinBasis_layers b₀ v₀ hlayers
  let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
    (D.filtration.squareLattice D.lattice) N hN hin hout
  refine ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeomQ, ?_⟩
  intro ε q χ hvert A hA hALip
  have hQ : Q.GeometryComplexityLE (squareGeometryBudget p) := hgeomQ
  have hm : (m : ℝ) ≤ squareGeometryBudget p := hgeom.1
  have hQ0 := squareGeometryBudget_nonneg hp
  have hObs0 := normalizedSquareObservableBudget_nonneg a b hp
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  let Hproj := ⌈Real.exp (p + 1)⌉₊
  have hproj := D.filtration.squareFinBasis_projection_height D.basis b₀ v₀ (hlayers 2)
    (one_le_ceil_exp (p + 1)) (fun i j => rationalHeightLE_ceil_exp (hb₀ j i))
  let P := coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin m)) Hproj
  have hP : (P : ℝ) ≤ Real.exp (normalizedSquareProjectionBudget p) := by
    have heq : normalizedSquareProjectionBudget p = (squareGeometryBudget p + p + 2 + 2) ^ 2 := by
      unfold normalizedSquareProjectionBudget
      ring
    rw [heq]
    apply coordinateLipschitzBound_le_exp _ _ Hproj
      (show 0 ≤ squareGeometryBudget p + p + 2 by linarith)
    · simpa only [Fintype.card_fin] using hT.1.1.trans (by linarith : p ≤ squareGeometryBudget p + p + 2)
    · simpa only [Fintype.card_fin] using hm.trans (by linarith : squareGeometryBudget p ≤ squareGeometryBudget p + p + 2)
    · exact (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
        (Real.exp_le_exp.mpr (by linarith))
  let ℓ := T.normBound * (T.lipBound * P) + T.normBound * (T.lipBound * (A * P))
  have hℓLip : letI := realificationQuotientMetricSpace bs (D.filtration.squareLattice D.lattice) N hN hout
      LipschitzWith ℓ (D.filtration.realSquareObservable D.lattice ε T.observable) :=
    D.filtration.realSquareObservable_lipschitz D.basis bs D.lattice D.grid N Hproj D.grid_pos hN
      D.outer_grid hout (fun k i => (hproj i k).1) (fun k i => (hproj i k).2)
      ε T.observable A T.lipBound T.normBound hALip T.lipschitz T.norm_le
  have hℓ : (ℓ : ℝ) ≤ Real.exp (normalizedSquareObservableBudget a b p) :=
    squareObservableLipschitz_le_exp A T.normBound T.lipBound P
      (normalizedSquareLeftBudget_nonneg a b hp) hA hB hK hP
  let H := ⌈Real.exp (squareGeometryBudget p)⌉₊
  have he (i j) : RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1)) (bs j)) i) H := by
    exact (quotientFinBasis_projection_height bs
      (D.filtration.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ v i}
      (hls (s + 1)) j i).mono (one_le_ceil_exp _)
  obtain ⟨S, hOrbit, hObs, hSB, hSK, hSval⟩ := D.filtration.exists_square_quotient_niltest_with_orbit D.lattice
    bs v hls N hN hin hout w q ε T.observable χ hvert ℓ T.normBound hℓLip T.norm_le
    H (one_le_ceil_exp _) he (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  let r := normalizedSquareReconstructionBudget a b p
  have hr : 0 ≤ r := normalizedSquareReconstructionBudget_nonneg a b hp
  have hQr : squareGeometryBudget p + 1 ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hUr : normalizedSquareObservableBudget a b p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hpr : 2 * p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hB2 : (((T.normBound ^ 2 : ℝ≥0) : ℝ)) ≤ Real.exp (2 * p) := by
    rw [NNReal.coe_pow]
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ T.normBound.coe_nonneg hB 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hSKBound : (S.lipBound : ℝ) ≤ Real.exp ((r + c) ^ c) := by
    rw [hSK]
    apply hrec _ _ H ℓ (T.normBound ^ 2) r hr
    · exact hm.trans (by linarith)
    · exact hQ.1.trans (by linarith)
    · exact (ceil_exp_le_exp_add_one hQ0).trans (Real.exp_le_exp.mpr hQr)
    · exact hℓ.trans (Real.exp_le_exp.mpr hUr)
    · exact hB2.trans (Real.exp_le_exp.mpr hpr)
  have hSBBound : (S.normBound : ℝ) ≤ Real.exp (2 * p) := by rw [hSB]; exact hB2
  have hlog := niltest_log_bound_of_exp S.normBound S.lipBound
    (by linarith : 0 ≤ 2 * p) (by positivity : 0 ≤ (r + c) ^ c) hSBBound hSKBound
  refine ⟨S, hOrbit, hObs, hSB, ?_, hSval⟩
  constructor
  · apply hQ.mono
    change squareGeometryBudget p ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    have hpow : 0 ≤ (r + c) ^ c := by positivity
    linarith
  · apply hlog.trans
    change 2 * p + (r + c) ^ c + 4 ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    linarith

theorem exists_square_niltest_with_budget_and_orbit {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c))
    (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p))
    (hALip : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
      (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, _, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  obtain ⟨S, hS⟩ := hconstruct ε q χ hvert A hA hALip
  exact ⟨_, D.filtration.squareFinBasis e ω (hF 2), squareFinWeight ω,
    D.filtration.squareFinBasis_layers e ω hF, N, hN, hin, hout, S, hS⟩

theorem exists_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c))
    (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p))
    (hALip : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
      (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest w, S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, _, _, hS⟩ :=
    D.exists_square_niltest_with_budget_and_orbit T hp hT a b c hrec ε q χ hvert A hA hALip
  exact ⟨m, bs, v, hls, N, hN, hin, hout, S, hS⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_specified_square_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d m : ℕ}
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
      (b : Basis (Fin m) ℚ L) (v : Fin m → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b v (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
      {ω : σ → ℕ} (T : D.Niltest ω) {p : ℝ},
      0 ≤ p → T.ComplexityLE p →
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ η : D.RealGroup, (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp p) →
      ∀ (q : D.filtration.squareFiltration.realification.PolynomialOrbit ω)
        (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest ω,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice η T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice η T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q)) := by
  obtain ⟨A, _, hobs⟩ := exists_specified_square_observable_lipschitz s
  obtain ⟨B, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let U := X + 1 + (X + Polynomial.C A) ^ A + 2 * X
  let P := X + 2 * X + (U + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d m _ _ _ _ D _ _ _ _ _ _ _ _ b v hF N hN hin hout ω T p hp hT hV hb η hη q χ hvert
  let bs := D.filtration.squareFinBasis b v (hF 2)
  let vs := squareFinWeight v
  let hls := D.filtration.squareFinBasis_layers b v hF
  let Q := D.filtration.squareFiltration.topQuotientModel bs vs hls
    (D.filtration.squareLattice D.lattice) N hN hin hout
  have hQ : Q.GeometryComplexityLE p :=
    D.filtration.squareFiltration.topQuotientModel_geometry bs vs hls
      (D.filtration.squareLattice D.lattice) N hN hin hout hp hV
  obtain ⟨ℓ, hℓ, hℓLip⟩ := hobs D b v (hF 2) N hN hout T hp hT hV.1 hb η hη
  let H := ⌈Real.exp p⌉₊
  have he (i j) : RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1)) (bs j)) i) H := by
    exact (quotientFinBasis_projection_height bs
      (D.filtration.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ vs i}
      (hls (s + 1)) j i).mono (one_le_ceil_exp p)
  obtain ⟨S, horbit, hobservable, hnorm, hlip, hval⟩ :=
    D.filtration.exists_square_quotient_niltest_with_orbit D.lattice bs vs hls N hN hin hout
      ω q η T.observable χ hvert ℓ T.normBound hℓLip T.norm_le H (one_le_ceil_exp p) he
      (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hB2 : ((T.normBound ^ 2 : ℝ≥0) : ℝ) ≤ Real.exp (2 * p) := by
    rw [NNReal.coe_pow]
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ T.normBound.coe_nonneg hB 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  let r := p + 1 + (p + A) ^ A + 2 * p
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp1r : p + 1 ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ p + A) A]
  have hAr : (p + A) ^ A ≤ r := by dsimp [r]; linarith
  have h2pr : 2 * p ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ p + A) A]
  have hlipBound : (S.lipBound : ℝ) ≤ Real.exp ((r + B) ^ B) := by
    rw [hlip]
    apply hrec _ _ H ℓ (T.normBound ^ 2) r hr
    · simpa only [Fintype.card_fin] using hV.1.trans (by linarith : p ≤ r)
    · exact hQ.1.trans (by linarith)
    · exact (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1r)
    · exact hℓ.trans (Real.exp_le_exp.mpr hAr)
    · exact hB2.trans (Real.exp_le_exp.mpr h2pr)
  have hnormBound : (S.normBound : ℝ) ≤ Real.exp (2 * p) := by rw [hnorm]; exact hB2
  have hlog := niltest_log_bound_of_exp S.normBound S.lipBound
    (by linarith : 0 ≤ 2 * p) (by positivity : 0 ≤ (r + B) ^ B) hnormBound hlipBound
  have hcost : p + 2 * p + (r + B) ^ B + 4 ≤ (p + C) ^ C := by
    simpa [X, U, P, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, horbit, hobservable, hnorm, ?_, hval⟩
  refine ⟨hQ.mono Q (by linarith [pow_nonneg (by positivity : 0 ≤ r + B) B]), ?_⟩
  exact hlog.trans (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_prescribed_two_shift_square_niltest (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d m : ℕ}
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
      (b : Basis (Fin m) ℚ L) (v : Fin m → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
      (M : ℕ) (hM : 0 < M)
      (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b v (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid M)
      {ω : σ → ℕ} (T : D.Niltest ω) {p : ℝ},
      0 ≤ p → T.ComplexityLE p →
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) M hM hin hout).GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ (a b₀ : σ → ℤ) (η γ : D.RealGroup), γ ∈ D.realLattice →
      (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + 2) ^ k)) →
      ∀ (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit ω)
        (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      (∀ x : σ → ℤ,
        D.filtration.realSquareFstHom
          (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq) =
            η⁻¹ * D.filtration.realification.polynomialOrbitEval ω (x + a) T.orbit * γ⁻¹ ∧
        D.filtration.realSquareSndHom
          (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq) =
            D.filtration.realification.polynomialOrbitEval ω (x + b₀) T.orbit) →
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) M hM hin hout
      ∃ S : Q.Niltest ω,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl rSq ∧
        S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b₀)) := by
  let A : ℕ := Classical.choose (exists_specified_square_niltest s)
  have hconstruct := @(Classical.choose_spec (exists_specified_square_niltest s)).2
  let X : Polynomial ℕ := Polynomial.X
  let V := X + (X + 2) ^ k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (V + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d m _ _ _ _ D _ _ _ _ _ _ _ _ b v hF M hM hin hout ω T p hp hT hV hb
    a b₀ η γ hγ hη rSq χ hvert hnorm
  let V₀ := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
    (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice) M hM hin hout
  let t := p + (p + 2) ^ k
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hkt : (p + 2) ^ k ≤ t := le_add_of_nonneg_left hp
  have ht : 0 ≤ t := hp.trans hpt
  have hbound : (t + A) ^ A ≤ (p + C) ^ C := by
    have hh : t + (t + A) ^ A ≤ (p + C) ^ C := by
      simpa [X, V, t, Polynomial.eval₂_pow] using hbudget p hp
    linarith
  obtain ⟨S, hSo, _, hSn, hSc, hSeval⟩ := hconstruct D b v hF M hM hin hout T ht
    (hT.mono hpt) (hV.mono V₀ hpt) (fun i j => (hb i j).trans hpt) η
    (fun i => (hη i).trans (Real.exp_le_exp.mpr hkt)) rSq χ hvert
  refine ⟨S, hSo, hSn, hSc.mono hbound, ?_⟩
  intro x
  exact (hSeval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice η γ
    (D.filtration.realification.polynomialOrbitEval ω (x + a) T.orbit)
    (D.filtration.realification.polynomialOrbitEval ω (x + b₀) T.orbit) hγ T.observable
    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq)
    (hnorm x).1 (hnorm x).2)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct NNReal

universe uσ uι uL

def NativeSquareNiltestSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (_hg : D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit)
    (χ : D.RealGroup → CircleFourier.Circle)
    (_hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x) (h : σ → ℤ),
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
          (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
          (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
          (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
          let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
            (D.filtration.squareLattice D.lattice) N hN hin hout
          ∃ S : Q.Niltest (fun _ : σ => 1),
            S.orbit = D.filtration.squareFiltration.nativeReducedPolynomialOrbit (fun _ => 1) r ∧
            (∀ z : D.filtration.squareFiltration.realification.Group,
              S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
                (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
                D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
            S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
            ∀ x : σ → ℤ, S.eval x = T.eval (fun i => x i + h i) * star (T.eval x)

theorem exists_native_square_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeSquareNiltestSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hnorm⟩ := exists_native_normalized_square.{uσ, uι, uL} s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨c₀, _, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C c₀) ^ c₀
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ e ω hF p hp T hT g hg χ hvert h
  have hsum : (p + 1 + a) ^ a + (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hεC : (p + 1 + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (p + c₀) ^ c₀)).trans hsum
  have hSC : (p + c₀) ^ c₀ ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 1 + a) ^ a)).trans hsum
  obtain ⟨ε, γ, hγ, hε, r, hf, hs, hderivative⟩ :=
    hnorm D e ω hF p hp hT.1 (fun i => (h i : ℚ)) g
  let q := D.filtration.squareFiltration.nativePolynomialOrbit (fun _ : σ => 1) r
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, hOrbit, hObs, hSB, hS, hSval⟩ :=
    D.exists_square_niltest_with_budget_and_orbit T hp hT a b c hrec ε q χ hvert A hA (hALip ε hε)
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hεC)), r, hf, hs, ?_,
    m, bs, v, hls, N, hN, hin, hout, S, hOrbit, hObs, hSB, hS.mono ((hbudget p hp).trans hSC), ?_⟩
  · simpa only [Rat.cast_intCast] using hderivative
  · intro x
    rw [hSval x]
    have hproduct := D.filtration.nativeNormalizedSquareObservable_product (fun _ => 1)
      D.lattice h ε γ hγ T.observable g r hf hs x
    rw [hg] at hproduct
    exact hproduct

end Erdos3

end

end OAI
