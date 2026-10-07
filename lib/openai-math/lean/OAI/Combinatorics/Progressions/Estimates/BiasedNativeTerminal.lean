import OAI.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped BigOperators

def SynchronizedNativeTerminalSpec (s C : ℕ) : Prop :=
  ∀ {σ ι τ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
    [LieRing L] [LieAlgebra ℚ L] {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l m : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hm : 0 < m) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hgrid : (D.grid : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hb : ∀ i j, RationalHeightLE (b.repr (D.basis j) i) H)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (v : τ → D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF)) (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (_hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF)).repr (v i) j) H)
    (η : D.filtration.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ D.filtration.fullFastGradedRelative b ω hF W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
    (_hbox : ∀ h ∈ S, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hdense : Real.exp (-p) * ∏ i, T i ≤ (S.card : ℝ))
    (_hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p p l m),
    ∃ A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      A * B * R = g ∧
      D.filtration.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord ∧
      D.filtration.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l R.coord ∧
      D.filtration.SymbolTerminalFactorization b ω hF W η T
        (D.filtration.realPolynomialSymbolHom b ω hF (fun _ => 1)
          (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) B)) ((p + C) ^ C)

theorem exists_synchronized_native_terminal (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeTerminalSpec s C := by
  obtain ⟨a, _, hcommon⟩ := exists_synchronized_native_common_coefficients s
  obtain ⟨b, _, hterminal⟩ := exists_unnormalized_common_symbolFactorization_bound s
  let Q : Polynomial ℕ := ((Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 1 + Polynomial.C a) ^ a
  let P : Polynomial ℕ := Polynomial.X + Q
  let R : Polynomial ℕ := P + (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ d D e ω hF H l m p hH hl hm hp hs hι hσ hτ hd hHp hlp hmp hgrid hc hb
    W v hv hW hh η hη T hT g S h₀ hh₀ hbox hdense hdata
  let q : ℝ := ((p + 2) ^ 3 + 3 * p + 1 + a) ^ a
  let r : ℝ := p + q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := add_nonneg hp hq
  have hpr : p ≤ r := le_add_of_nonneg_right hq
  have hqr : q ≤ r := le_add_of_nonneg_left hp
  have hterminalPos : 0 ≤ (r + b) ^ b := by positivity
  have hbound : r + (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [R, P, Q, r, q, Polynomial.eval₂_pow] using hfinal p hp
  have hterminalC : (r + b) ^ b ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨n, hn, hnq, _, _, A, B, D₀, small, rational, Z, hprod, hB, hA, hD, _, _, _, hgood⟩ :=
    hcommon D e ω hF H l m p hH hl hm hp hι hσ hd hHp hlp hmp hgrid hc hb
      T hTpos g S h₀ hh₀ W hbox hdata
  let B' : D.filtration.realFastDiagonalSubgroup (fun _ : σ => 1)
      (D.filtration.fastPointwiseSquare e ω hF (fun _ => 1) W) := ⟨B, hB⟩
  have hfactor := hterminal D.filtration e ω hF W H r hH hr hs
    (hι.trans hpr) (hσ.trans hpr) (hτ.trans hpr) (hHp.trans (Real.exp_le_exp.mpr hpr)) hc
    hW v hv hh η hη B' T (fun i => (Real.exp_le_exp.mpr hterminalC).trans (hT i))
    (Real.exp q) (Real.exp_nonneg q) (Real.exp_le_exp.mpr hqr)
    n hn (hnq.trans (Real.exp_le_exp.mpr hqr)) S h₀ hh₀ small rational Z
    hbox (fun h hh => (hgood h hh).1) (fun h hh => (hgood h hh).2.1) (fun h hh => (hgood h hh).2.2)
    (Real.exp (-p)) (Real.exp_pos _) (by
      simpa only [Real.exp_neg, inv_inv] using Real.exp_le_exp.mpr hpr) hdense
  exact ⟨A, B, D₀, hprod, hA, hD,
    SymbolTerminalFactorization.mono D.filtration e ω hF W hfactor hterminalC hTpos⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedNativeTerminalSpec (s C : ℕ) : Prop :=
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
        ∃ (l : ℕ) (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
          (A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ A * B * R = g ∧
          D.filtration.RealAdaptedCoefficientBound e ω hF (fun _ => 1)
            (fun i => (lengths i : ℝ)) (Real.exp ((p + C) ^ C)) A.coord ∧
          D.filtration.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l R.coord ∧
          D.filtration.SymbolTerminalFactorization e ω hF W (D.filtration.gradedFrequency e ω hF η)
            (fun i => (lengths i : ℝ))
            (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
              (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) B)) ((p + C) ^ C)

theorem exists_biased_native_terminal (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedNativeTerminalSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_biased_synchronized_square_family s c hI
  obtain ⟨b, _, hterminal⟩ := exists_synchronized_native_terminal s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + (Polynomial.X + 4) ^ 5 + G + Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + (p + 4) ^ 5 + squareGeometryBudget p + p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h11 : 0 ≤ (p + 4) ^ 11 := by positivity
  have h5 : 0 ≤ (p + 4) ^ 5 := by positivity
  have hgeom := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have h11q : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have h5q : (p + 4) ^ 5 ≤ q := by dsimp [q]; linarith
  have hGq : squareGeometryBudget p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hlast : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, k, q, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hqC : q + 1 ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  have hkq1 : k ≤ q + 1 := by linarith
  have hpq1 : p ≤ q + 1 := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, hinverse, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨S, h₀, l, m, W, u, hh₀, hcount, hl, hlk, hm, hmk, _, hu, hW, hheight, hη, hshift, hdata⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHp : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans h11q)
  have hb : ∀ i j, RationalHeightLE (e.repr (D.basis j) i) H :=
    fun i j => rationalHeightLE_ceil_exp ((hinverse j i).trans h5q)
  have hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) H :=
    fun i j => rationalHeightLE_ceil_exp ((hheight i j).trans hkq)
  have hτ : (Fintype.card (Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) : ℝ) ≤ q + 1 := by
    rw [Fintype.card_fin]
    exact hgeometry.1.trans (hGq.trans (by linarith))
  have hdense : Real.exp (-(q + 1)) * (∏ i, (lengths i : ℝ)) ≤ S.card :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkq1))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  have hdata' := RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono
    D e ω hF hdata hkq1 hkq1 hTpos
  obtain ⟨A, M, R, hprod, hA, hR, hfactor⟩ := hterminal D e ω hF H l m (q + 1)
    hH hl hm hq1 hs (hdim.trans hpq1) (hσ.trans hpq1) hτ (hT.1.1.trans hpq1) hHp
    (hlk.trans (Real.exp_le_exp.mpr hkq1)) (hmk.trans (Real.exp_le_exp.mpr hkq1))
    (hT.1.2.1.trans (Real.exp_le_exp.mpr hpq1)) hc hb W u hu hW hh
    (D.filtration.gradedFrequency e ω hF η) hη (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) g S h₀ hh₀
    (fun h hh => (hshift h hh).1) hdense hdata'
  exact ⟨l, W, A, M, R, hl, hlk.trans (Real.exp_le_exp.mpr hkC), hprod,
    D.filtration.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1)
      (fun i => (lengths i : ℝ)) hTpos (Real.exp_le_exp.mpr hqC) A.coord hA, hR,
    SymbolTerminalFactorization.mono D.filtration e ω hF W hfactor hbC hTpos⟩

theorem exists_stepTwo_biased_native_terminal :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedNativeTerminalSpec.{uσ, uL} 1 C :=
  exists_biased_native_terminal 1 4 translatedStepDropSpec_one

end Erdos3

end

end OAI
