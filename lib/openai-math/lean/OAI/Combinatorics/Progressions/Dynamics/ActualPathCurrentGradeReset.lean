import OAI.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization

namespace OAI

section

namespace Erdos3

theorem exists_actual_path_reset_budget (a cr cs ct : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let z := (p + cr) ^ cr + (p + 2) ^ a + p + 2
      (p + cr) ^ cr ≤ (p + C) ^ C ∧
        (z + cs) ^ cs ≤ (p + C) ^ C ∧
        (z + ct) ^ ct ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C cr) ^ cr
  let Z : Polynomial ℕ := P + (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let S : Polynomial ℕ := (Z + Polynomial.C cs) ^ cs
  let T : Polynomial ℕ := (Z + Polynomial.C ct) ^ ct
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + S + T)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hbound := hbudget p hp
  have hP := natPolynomial_eval_nonneg P hp
  have hS := natPolynomial_eval_nonneg S hp
  have hT := natPolynomial_eval_nonneg T hp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add] at hbound
  have hparts : P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      S.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      T.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C :=
    ⟨by linarith, by linarith, by linarith⟩
  simpa only [P, Z, S, T, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom, Nat.cast_ofNat] using hparts

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolPointwiseSubalgebra_basisGraded [Fintype τ] [Fintype ι]
    (v : τ → ℕ) (hv : ∀ i, 0 < v i) (U : LieSubalgebra ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.polynomialSymbolBasis b ω hF v)
      (fun z => ω z.val.2) (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule := by
  let : Fintype (SymbolBasisIndex v ω) :=
    symbolBasisIndexFintype v ω s hv (F.adaptedBasis_weight_le_step b ω hF)
  have h := (F.symbolPointwiseSubalgebra_blockInvariant b ω hF v U).graded
    (F.polynomialSymbolBasis b ω hF v) (fun z => z.val.1)
    (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule (Finsupp.weight v)
  have he : (fun z : SymbolBasisIndex v ω => Finsupp.weight v z.val.1) =
      (fun z => ω z.val.2) := funext (fun z => z.property)
  rw [he] at h
  exact h

theorem exists_restricted_path_common_quotient_splitting
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈
        realificationLieSubalgebra U)
    (El Pl Rl : F.RealPolynomialSymbolGroup v)
    (hlocal : El * Pl * Rl = F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ Z) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    ∃ P₀ : F.RealPolynomialSymbolGroup v,
      F.realSymbolGradeQuotientHom v k P₀ ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
          (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) ∧
      pull E * P₀ * pull R = El * Pl * Rl := by
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
  refine ⟨(pull E)⁻¹ * pull Z * (pull R)⁻¹,
    F.homogeneousPullback_residual_quotient_mem b ω hF w v β hβ U K hK E Z R k hx, ?_⟩
  rw [hlocal]
  change pull E * ((pull E)⁻¹ * pull Z * (pull R)⁻¹) * pull R = pull Z
  group

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial

theorem exists_symbol_reset_from_restricted_path (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (v : τ → ℕ), (∀ i, 0 < v i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : τ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded) (vg : κ → F.PolynomialSymbol v),
        Submodule.span ℚ (Set.range vg) = (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule →
        (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF v).repr (vg i) z) H) →
        ∀ {σ : Type*} (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ),
        ∀ hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i),
        ∀ K : Set (σ → ℝ), (∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K) →
        ∀ (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ), k ≤ s + 1 →
        (∀ t ∈ K, ∀ j < k, F.realSymbolGradeEvaluation b ω hF w j t
          (E⁻¹ * Z * R⁻¹).coord ∈ realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup v),
        El * Pl * Rl = pull Z →
        Pl.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF v l Rl → F.SymbolRationalGrid b ω hF v l (pull R) →
        let A := F.truncateRealSymbol b ω hF v k ((pull E)⁻¹ * El)
        let D := F.truncateRealSymbol b ω hF v k (Rl * (pull R)⁻¹)
        (El * A⁻¹) * (A * Pl * D) * (D⁻¹ * Rl) = El * Pl * Rl ∧
          (A * Pl * D).coord ∈ realificationLieSubalgebra
            (F.symbolPointwiseSubalgebra b ω hF v U) ∧
          F.realSymbolGradeQuotientHom v k (El * A⁻¹) = F.realSymbolGradeQuotientHom v k (pull E) ∧
          F.realSymbolGradeQuotientHom v k (D⁻¹ * Rl) = F.realSymbolGradeQuotientHom v k (pull R) ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) (El * A⁻¹) ∧
          F.SymbolRationalGrid b ω hF v m (D⁻¹ * Rl) := by
  obtain ⟨C, hC, hreset⟩ := exists_symbol_reset_from_common_quotient s a
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T hT
  obtain ⟨m, hm, hmp, hlm, hresetm⟩ :=
    hreset F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro U vg hspan hvg σ w β hβ K hK E Z R k hk hx
  dsimp only
  intro El Pl Rl hlocal hPl hEl hE hRl hR
  obtain ⟨P₀, hP₀, hidentity⟩ := F.exists_restricted_path_common_quotient_splitting
    b ω hF w v β hβ U K hK E Z R k hx El Pl Rl hlocal
  exact hresetm (F.symbolPointwiseSubalgebra b ω hF v U) vg hspan
    (F.symbolPointwiseSubalgebra_basisGraded b ω hF v hv U) hvg k hk El Pl Rl
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ E) P₀
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ R)
    hPl hP₀ (congrArg (F.realSymbolGradeQuotientHom v k) hidentity) hEl hE hRl hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_actual_path_common_quotient_splitting
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ,
      (fun i => MvPolynomial.eval u (weightedHomogeneousComponent v (w i) (β i))) ∈ K)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t
        (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U)
    (El Pl Rl : F.RealPolynomialSymbolGroup v)
    (hlocal : El * Pl * Rl = F.realPolynomialSymbolHom b ω hF v
      (F.weightedAdaptedRealChartHom w v β hβ g)) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
      (fun i => weightedHomogeneousComponent v (w i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    ∃ P₀ : F.RealPolynomialSymbolGroup v,
      F.realSymbolGradeQuotientHom v k P₀ ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
          (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) ∧
      pull E * P₀ * pull R = El * Pl * Rl := by
  have hactual := F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF w v β hβ g
  exact F.exists_restricted_path_common_quotient_splitting b ω hF w v
    (fun i => weightedHomogeneousComponent v (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    U K hK E (F.realPolynomialSymbolHom b ω hF w g) R k hx El Pl Rl (hlocal.trans hactual)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial MvPolynomial

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem exists_actual_path_current_grade_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (v : τ → ℕ), (∀ i, 0 < v i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : τ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded) (vg : κ → F.PolynomialSymbol v),
        Submodule.span ℚ (Set.range vg) = (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule →
        (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF v).repr (vg i) z) H) →
        ∀ {σ : Type*} (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ),
        ∀ hβ : ∀ i, β i ∈ weightedSupportLE v (w i),
        ∀ K : Set (σ → ℝ),
        (∀ u : τ → ℝ,
          (fun i => MvPolynomial.eval u (weightedHomogeneousComponent v (w i) (β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
          (E R : F.RealPolynomialSymbolGroup w) (k : ℕ), k ≤ s + 1 →
        (∀ t ∈ K, ∀ j < k, F.realSymbolGradeEvaluation b ω hF w j t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
          (fun i => weightedHomogeneousComponent v (w i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup v),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF v
          (F.weightedAdaptedRealChartHom w v β hβ g) →
        Pl.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF v l Rl → F.SymbolRationalGrid b ω hF v l (pull R) →
        ∃ E' P' R' : F.RealPolynomialSymbolGroup v,
          E' * P' * R' = F.realPolynomialSymbolHom b ω hF v
            (F.weightedAdaptedRealChartHom w v β hβ g) ∧
          P'.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) ∧
          F.realSymbolGradeQuotientHom v k (pull E) = F.realSymbolGradeQuotientHom v k E' ∧
          F.realSymbolGradeQuotientHom v k R' = F.realSymbolGradeQuotientHom v k (pull R) ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) E' ∧
          F.SymbolRationalGrid b ω hF v m R' ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) ((pull E)⁻¹ * E') ∧
          F.SymbolRationalGrid b ω hF v m (R' * (pull R)⁻¹) := by
  obtain ⟨cr, _, hreset⟩ := exists_symbol_reset_from_common_quotient s a
  obtain ⟨cs, _, hslowprod⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨ct, _, hratprod⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨C, hC, hbudget⟩ := exists_actual_path_reset_budget a cr cs ct
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T hT
  let z : ℝ := (p + cr) ^ cr + (p + 2) ^ a + p + 2
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpz : p ≤ z := by dsimp [z]; linarith
  have hrz : (p + cr) ^ cr ≤ z := by dsimp [z]; linarith
  have haz : (p + 2) ^ a ≤ z := by dsimp [z]; linarith
  have hbud := hbudget p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m₁, hm₁, hm₁bound, hlm₁, hresetm⟩ :=
    hreset F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T
      (fun i => (Real.exp_le_exp.mpr hbud.1).trans (hT i))
  obtain ⟨m₂, hm₂, hm₂bound, hm₁m₂, hproducts⟩ := hratprod F b ω hF v hv H z hH hz
    (hι.trans hpz) (hτ.trans hpz) (hHp.trans (Real.exp_le_exp.mpr hpz)) hb m₁ hm₁
    (hm₁bound.trans (Real.exp_le_exp.mpr hrz))
  refine ⟨m₂, hm₂, hm₂bound.trans (Real.exp_le_exp.mpr hbud.2.2), hlm₁.trans hm₁m₂, ?_⟩
  intro U vg hspan hvg σ w β hβ K hK g E R k hk hx
  dsimp only
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
    (fun i => weightedHomogeneousComponent v (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  intro El Pl Rl hlocal hPl hEl hE hRl hR
  obtain ⟨P₀, hP₀, hidentity⟩ := F.exists_actual_path_common_quotient_splitting
    b ω hF w v β hβ U K hK g E R k hx El Pl Rl hlocal
  obtain ⟨hprod, hmid, hEq, hRq, hslow, hgrid⟩ := hresetm
    (F.symbolPointwiseSubalgebra b ω hF v U) vg hspan
    (F.symbolPointwiseSubalgebra_basisGraded b ω hF v hv U) hvg k hk El Pl Rl
    (pull E) P₀ (pull R) hPl hP₀
    (congrArg (F.realSymbolGradeQuotientHom v k) hidentity) hEl hE hRl hR
  let A := F.truncateRealSymbol b ω hF v k ((pull E)⁻¹ * El)
  let D := F.truncateRealSymbol b ω hF v k (Rl * (pull R)⁻¹)
  have hslowdiff : F.SymbolSlowBound b ω hF v T
      (Real.exp ((p + C) ^ C)) ((pull E)⁻¹ * (El * A⁻¹)) := by
    have hinput : ∀ x ∈ [(pull E)⁻¹, El * A⁻¹],
        F.SymbolSlowBound b ω hF v T (Real.exp ((z + 2) ^ 1)) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · apply (F.symbolSlowBound_inv_iff b ω hF v T _ _).mpr
        exact F.symbolSlowBound_mono b ω hF v T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using haz.trans (by linarith : z ≤ z + 2)))
          _ hE
      · exact F.symbolSlowBound_mono b ω hF v T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using hrz.trans (by linarith : z ≤ z + 2)))
          _ hslow
    have h := hslowprod F b ω hF v hv H z hH hz (hι.trans hpz) (hτ.trans hpz)
      (hHp.trans (Real.exp_le_exp.mpr hpz)) hb T hTpos [(pull E)⁻¹, El * A⁻¹] (by simp) hinput
    simp only [List.prod_cons, List.prod_nil, mul_one] at h
    exact F.symbolSlowBound_mono b ω hF v T hTpos (Real.exp_le_exp.mpr hbud.2.1) _ h
  have hgriddiff : F.SymbolRationalGrid b ω hF v m₂ ((D⁻¹ * Rl) * (pull R)⁻¹) := by
    have hinput : ∀ x ∈ [D⁻¹ * Rl, (pull R)⁻¹], F.SymbolRationalGrid b ω hF v m₁ x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hgrid
      · exact F.symbolRationalGrid_inv b ω hF v m₁
          (F.symbolRationalGrid_mono b ω hF v hl hlm₁ _ hR)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts [D⁻¹ * Rl, (pull R)⁻¹] (by simp) hinput
  exact ⟨El * A⁻¹, A * Pl * D, D⁻¹ * Rl, hprod.trans hlocal, hmid, hEq.symm, hRq,
    F.symbolSlowBound_mono b ω hF v T hTpos (Real.exp_le_exp.mpr hbud.1) _ hslow,
    F.symbolRationalGrid_mono b ω hF v hm₁ hm₁m₂ _ hgrid, hslowdiff, hgriddiff⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
