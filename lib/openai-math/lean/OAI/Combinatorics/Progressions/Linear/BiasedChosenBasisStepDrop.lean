import OAI.Combinatorics.Progressions.Estimates.BiasedNativeTerminal

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedChosenBasisStepDropSpec (s C : ℕ) : Prop :=
  ∀ (_hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
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
        D.filtration.ControlledSymbolFactorization e ω hF η (fun i => (lengths i : ℝ))
          (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
            (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) g)) ((p + C) ^ C)

theorem exists_biased_chosen_basis_step_drop (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedChosenBasisStepDropSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_biased_native_terminal s c hI
  obtain ⟨b, _, hcompose⟩ := exists_controlled_symbol_composition (s + 1)
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h11 : 0 ≤ (p + 4) ^ 11 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have h11q : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hlast : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, k, q, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  have hkq1 : k ≤ q + 1 := by linarith
  have hpq1 : p ≤ q + 1 := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, _, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨l, W, A, M, R, hl, hlk, hprod, hA, hR, hterminal⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHp : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans h11q)
  let φ : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1) →*
      D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1) :=
    (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)).comp
      (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1))
  have hinner : D.filtration.ControlledSymbolFactorization e ω hF η
      (fun i => (lengths i : ℝ)) (φ M) (k + 1) :=
    SymbolTerminalFactorization.controlled D.filtration e ω hF W hk hTpos hterminal
  have hinner' := ControlledSymbolFactorization.mono D.filtration e ω hF hinner
    (show k + 1 ≤ q + 1 by linarith) hTpos
  have houter : D.filtration.SymbolSlowBound e ω hF (fun _ => 1)
      (fun i => (lengths i : ℝ)) (Real.exp (q + 1)) (φ A) :=
    D.filtration.symbolSlowBound_mono e ω hF (fun _ => 1) (fun i => (lengths i : ℝ)) hTpos
      (Real.exp_le_exp.mpr hkq1) (φ A)
      (D.filtration.native_symbol_slow e ω hF (fun _ => 1) (fun i => (lengths i : ℝ)) hTpos
        (Real.exp_nonneg k) A hA)
  have hrat : D.filtration.SymbolRationalGrid e ω hF (fun _ => 1) l (φ R) :=
    D.filtration.native_symbol_grid e ω hF (fun _ => 1) l R hR
  have hfull := hcompose D.filtration e ω hF H (q + 1) hH hq1
    (hdim.trans hpq1) (hσ.trans hpq1) hHp hc (fun i => (lengths i : ℝ)) hTpos η
    l hl (hlk.trans (Real.exp_le_exp.mpr hkq1)) (φ A) (φ M) (φ R) houter hrat hinner'
  have heq : φ A * φ M * φ R = φ g := by
    rw [← map_mul, ← map_mul, hprod]
  rw [heq] at hfull
  exact ControlledSymbolFactorization.mono D.filtration e ω hF hfull hbC hTpos

theorem exists_stepTwo_chosen_basis_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedChosenBasisStepDropSpec.{uσ, uL} 1 C :=
  exists_biased_chosen_basis_step_drop 1 4 translatedStepDropSpec_one

end Erdos3

end

end OAI
