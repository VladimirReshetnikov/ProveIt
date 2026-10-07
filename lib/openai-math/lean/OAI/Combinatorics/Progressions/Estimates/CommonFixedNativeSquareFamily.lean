import OAI.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
import OAI.Combinatorics.Progressions.Linear.BasisFamilyLogHeight

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def UniformNativeBiasedSquareSpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
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
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (h : σ → ℤ) (A : Finset (σ → ℤ)), A.Nonempty →
        Real.exp (-(2 * p + 1)) ≤ ‖𝔼 x ∈ A, T.eval (x + h) * star (T.eval x)‖ →
        D.HasNativeBiasedSquareInModel
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η A h ((p + C) ^ C)

theorem exists_uniform_native_biased_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ UniformNativeBiasedSquareSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hnorm⟩ := exists_native_normalized_square.{uσ, 0, uL} s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨d, _, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  obtain ⟨v, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C d) ^ d +
    (Polynomial.X + 1 + Polynomial.C a) ^ a + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := R + (R + Polynomial.C v) ^ v + 2 * Polynomial.X + 2
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ n _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let q := (p + d) ^ d + (p + 1 + a) ^ a + 2 * p + 2
  have hd0 : 0 ≤ (p + d) ^ d := by positivity
  have ha0 : 0 ≤ (p + 1 + a) ^ a := by positivity
  have hdq : (p + d) ^ d ≤ q := by dsimp [q]; linarith
  have haq : (p + 1 + a) ^ a ≤ q := by dsimp [q]; linarith
  have hpq : 2 * p + 2 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hv := hvertical q hq
  have hpow : 0 ≤ (q + v) ^ v := by positivity
  have hfinal' : q + (q + v) ^ v + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [P, R, q, Polynomial.eval₂_pow] using hfinal p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hvC : verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  have hbC : 2 * p + 2 + verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  obtain ⟨A₀, _, hA₀, hLip⟩ := hleft D p hp hT.1
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert h A hA hbias
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative⟩ :=
    hnorm D e ω hF p hp hT.1 (fun i => (h i : ℚ)) g
  let qr := D.filtration.squareFiltration.nativePolynomialOrbit (fun _ : σ => 1) r
  obtain ⟨S, hOrbit, hObs, _, hS, hSval⟩ := hconstruct ε qr
    (fun z => ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle))
    hvert A₀ hA₀ (hLip ε hε)
  have hEval (x : σ → ℤ) : S.eval x = T.eval (x + h) * star (T.eval x) := by
    apply (hSval x).trans
    have hprod := D.filtration.nativeNormalizedSquareObservable_product (fun _ => 1)
      D.lattice h ε γ hγ T.observable g r hf hsecond x
    rw [hg] at hprod
    exact hprod
  have herror : (Real.exp (-(2 * p + 1)) / 2)⁻¹ ≤ Real.exp q := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp (2 * p + 1) := by rw [inv_div, Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (2 * p + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hpq
  have hc : Real.exp (-(2 * p + 1)) ≤ ‖finiteCorrelation A (fun _ => 1) S.eval‖ := by
    rw [norm_finiteCorrelation_one]
    have hmean : (𝔼 x ∈ A, S.eval x) = 𝔼 x ∈ A, T.eval (x + h) * star (T.eval x) :=
      Finset.expect_congr rfl (fun x _ => hEval x)
    rw [hmean]
    exact hbias
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hrestriction, hCorr⟩ :=
    D.filtration.exists_correlating_square_vertical_mode D.lattice
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hs (fun _ : σ => 1) ε η T.observable hvert r S hOrbit hObs hq
      (hS.mono ((hbudget p hp).trans hdq)) (Real.exp_pos _) herror hA
      (fun _ => 1) (fun _ _ => by norm_num) hc
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr (haq.trans hqC))),
    r, hf, hsecond, ?_, ξ, V, hVO, hV.mono hqC,
    (fun i => (hheight i).trans hvC), hchar, hint, hrestriction, ?_⟩
  · simpa only [Rat.cast_intCast] using hderivative
  · rw [norm_finiteCorrelation_one] at hCorr
    apply le_trans _ hCorr
    calc
      _ ≤ Real.exp ((-(2 * p + 1) - verticalDecompositionBudget q) - 1) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ Real.exp (-(2 * p + 1) - verticalDecompositionBudget q) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [Real.exp_sub]; ring

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def CommonNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ H : Finset (σ → ℤ), H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasNativeBiasedSquareInModel
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (derivativeSupport (translatedIntegerBox origin lengths) h) h ((p + C) ^ C)

theorem exists_common_native_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hsingle⟩ := exists_uniform_native_biased_square.{uσ, uL} s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + 5 * Polynomial.X + 6
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ n _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  have hbound : (p + a) ^ a + 5 * p + 6 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  have h5 : 5 * p + 6 ≤ (p + C) ^ C := by linarith
  have h4 : 4 * p + 6 ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hsingle hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert origin lengths hlengths hσ hbias
  obtain ⟨H, hH, hcount, hgood⟩ := exists_many_biased_box_shifts origin lengths hlengths T.eval hp hσ
    (fun x _ => T.eval_budget hT x) hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h4))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hmean⟩ := hgood h hh
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h5))
        (Nat.cast_nonneg (lengths i))).trans_lt (hsides i)
    · have hA : (derivativeSupport (translatedIntegerBox origin lengths) h).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.expect_empty, norm_zero] at hmean
        exact (not_le_of_gt (Real.exp_pos _)) hmean
      exact RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        (hconstruct g hg η hvert h (derivativeSupport (translatedIntegerBox origin lengths) h) hA hmean) haC

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

namespace RationalFilteredNilmanifold

theorem HasNativeFactoredSquareInModel.mono
    {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    {hs : 1 ≤ s} {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p q p' q' : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p q)
    (hpp : p ≤ p') (hqq : q ≤ q') (hS : ∀ i, 0 < S i) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p' q' := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpp)), r,
    hf, hsecond, hderivative, ξ, (fun i => (hheight i).trans hpp), hrestriction, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ _ _ _ hfactor hqq hS

theorem HasNativeFactoredSquareInModel.rescale
    {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    {hs : 1 ≤ s} {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ} {h : σ → ℤ} {p q r : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p q)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hr : 0 ≤ r) (hST : ∀ i, Real.exp (-r) * T i ≤ S i) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η T h p (q + (s : ℝ) * r) := by
  obtain ⟨ε, γ, hγ, hε, a, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  refine ⟨ε, γ, hγ, hε, a, hf, hsecond, hderivative, ξ, hheight, hrestriction, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.rescale _ _ _ _ hfactor hS hT hr hST

end RationalFilteredNilmanifold

def InductiveNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ H : Finset (σ → ℤ), H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasNativeFactoredSquareInModel
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (fun i => (lengths i : ℝ)) h ((p + C) ^ C) ((p + C) ^ C)

theorem exists_inductive_native_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ InductiveNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, ha, hfamily⟩ := exists_common_native_square_family.{uσ, uL} s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P : Polynomial ℕ := B + ((B + Polynomial.C c) ^ c + Polynomial.C s * B)
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let q : ℝ := (p + a) ^ a
  let r : ℝ := (q + c) ^ c
  let t : ℝ := r + (s : ℝ) * q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbound : q + t ≤ (p + C) ^ C := by
    simpa [P, B, q, r, t, Polynomial.eval₂_pow] using hfinal p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right ht).trans hbound
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  have hqr : q + r ≤ (p + C) ^ C := by
    have hrt : r ≤ t := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hq)
    exact (add_le_add (le_refl q) hrt).trans hbound
  have hpq : p ≤ q := by
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
    apply (show p ≤ p + a by linarith).trans
    exact (pow_one (p + a)).symm.le.trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + a) (by omega : 1 ≤ a))
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hfamily hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert origin lengths hlengths hσ hlarge hbias
  obtain ⟨H, hH, hcount, hgood⟩ := hconstruct g hg η hvert origin lengths hlengths hσ hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hdata⟩ := hgood h hh
    have hlargeOverlap : ∀ i, Real.exp r ≤ (((lengths i : ℤ) - |h i|).toNat : ℝ) := by
      intro i
      have hsize : Real.exp (q + r) ≤ (lengths i : ℝ) :=
        (Real.exp_le_exp.mpr hqr).trans (hlarge i)
      have heq : Real.exp r = Real.exp (-q) * Real.exp (q + r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le).trans (hsides i).le
    have hpos : ∀ i, 0 < ((lengths i : ℤ) - |h i|).toNat := by
      intro i
      have hposR := (Real.exp_pos r).trans_le (hlargeOverlap i)
      exact_mod_cast hposR
    rw [derivativeSupport_translatedIntegerBox] at hdata
    have hfactor := RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.factorization D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hI hq (hσ.trans hpq) hpos hlargeOverlap hdata
    have hscaled := RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.rescale D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hfactor
      (fun i => by exact_mod_cast hpos i) (fun i => by exact_mod_cast hlengths i)
      hq (fun i => (hsides i).le)
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
        (Nat.cast_nonneg (lengths i))).trans_lt (hsides i)
    · exact RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        hscaled hqC htC (fun i => by exact_mod_cast hlengths i)

theorem exists_stepTwo_native_square_family :
    ∃ C : ℕ, 2 ≤ C ∧ InductiveNativeSquareFamilySpec.{uσ, uL} 1 C :=
  exists_inductive_native_square_family 1 4 translatedStepDropSpec_one

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def CommonFixedNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF)
          (D.filtration.squareLattice D.lattice) N hN hin hout
        let ν := quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}
        let hQ := D.filtration.squareFiltration.topQuotientModel_basis_layers
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF)
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (H : Finset (σ → ℤ)) (l : ℕ) (W : LieSubalgebra ℚ Q.filtration.AssociatedGraded)
          (u : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) → Q.filtration.AssociatedGraded),
          H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule (Q.filtration.associatedGradedBasis Q.basis ν hQ) ν W.toSubmodule ∧
          BasisFamilyLogHeight (Q.filtration.associatedGradedBasis Q.basis ν hQ) u ((p + C) ^ C) ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasFixedNativeSquareFactors
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (fun i => (lengths i : ℝ)) h ((p + C) ^ C) l W

theorem exists_common_fixed_native_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonFixedNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_inductive_native_square_family s c hI
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + G
  let P : Polynomial ℕ := B + ((Q + 2) ^ 5 + Q) + Q
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let b : ℝ := (p + a) ^ a
  let q : ℝ := b + squareGeometryBudget p
  let k : ℝ := (q + 2) ^ 5 + q
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := add_nonneg hb hg
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbound : b + k + q ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, b, q, k, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hbkC : b + k ≤ (p + C) ^ C := by linarith
  have hbq : b ≤ q := le_add_of_nonneg_right hg
  have hgq : squareGeometryBudget p ≤ q := le_add_of_nonneg_left hb
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hfamily hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨H, hH, hcount, hgood⟩ := hconstruct g hgOrbit η hvert origin lengths hlengths hσ
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) hbias
  have hdata : ∀ h ∈ H, D.HasNativeFactoredSquareInModel
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h q q := by
    intro h hh
    exact RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      (hgood h hh).2.2 hbq hbq hTpos
  obtain ⟨l, W, u, H', hsub, hH', hlarge', hl, hlq, hu, hW, hheight, hfixed⟩ :=
    D.exists_common_native_square_factors
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hs g η (fun i => (lengths i : ℝ)) H hH hq (hgeom.1.trans hgq) hdata
  refine ⟨H', l, W, u, hH', ?_, hl, hlq.trans (Real.exp_le_exp.mpr hqC), hu, hW,
    ?_, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤
          Real.exp (-(b + k)) * (∏ i, (lengths i : ℝ)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbkC))
          (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))
      _ = Real.exp (-k) * (Real.exp (-b) * (∏ i, (lengths i : ℝ))) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-k) * H.card := mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
      _ ≤ H'.card := hlarge'
  · intro i j
    exact (hheight i j).trans hqC
  · intro h hh
    have hprior := hgood h (hsub hh)
    refine ⟨hprior.1, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbC))
        (Nat.cast_nonneg (lengths i))).trans_lt (hprior.2.1 i)
    · exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        (hfixed h hh) hqC hTpos

theorem exists_stepTwo_common_fixed_square_family :
    ∃ C : ℕ, 2 ≤ C ∧ CommonFixedNativeSquareFamilySpec.{uσ, uL} 1 C :=
  exists_common_fixed_native_square_family 1 4 translatedStepDropSpec_one

end Erdos3

end

end OAI
