import OAI.Combinatorics.Progressions.Estimates.UniformFormalCurrentLayerStep
import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialOperationBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_derivative_removal_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
      BasisHomogeneousBrackets b ω →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
      A.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) →
      B.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
      CoefficientGrid (b.baseChange ℝ) l B.coord →
      ∀ {κ : Type*} (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
        (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      (∀ k, S k ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ k, R k ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ k, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) (S k)) →
      (∀ k, CoefficientGrid (b.baseChange ℝ) l (R k)) →
      (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a) / T i) (small i)) →
      (∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)) →
      (∀ k, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (dualAdjoint A⁻¹ (S k)) ∧
        CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (R k))) ∧
      (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i)
          (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) ∧
        CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (rational i) - formalLogDerivative i B)) ∧
      (∀ k, dualAdjoint A⁻¹ (S k) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 ∧
        dualAdjoint B (R k) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) ∧
      ∀ i, dualAdjoint A⁻¹ (small i - formalLogDerivative i A) ∈
          shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 ∧
        dualAdjoint B (rational i) - formalLogDerivative i B ∈
          shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 := by
  obtain ⟨D, _, hbound⟩ := exists_formal_polynomial_operation_bound s a
  obtain ⟨E, _, hgrid⟩ := exists_formal_polynomial_operation_grid s
  let P : Polynomial ℕ := 2 * (Polynomial.X + Polynomial.C D) ^ D +
    (Polynomial.X + 2) ^ a + (Polynomial.X + Polynomial.C E) ^ E + Polynomial.C (s + 2)
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF hgraded H p hH hp hι hσ hHp hc l hl hlp
  have hbig : 2 * (p + D) ^ D + (p + 2) ^ a + (p + E) ^ E + (s + 2 : ℝ) ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hCbound p hp
  let d := (p + D) ^ D
  let n := (p + 2) ^ a
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have he : 0 ≤ (p + E) ^ E := by positivity
  have hgridCap : (p + E) ^ E ≤ (p + C) ^ C := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hliftCap : d + n ≤ (p + C) ^ C := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hremCap : 2 * d + n + (s + 1 : ℝ) ≤ (p + C) ^ C := by
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hslowCap : Real.exp d * (Real.exp n + Real.exp d * ((s : ℝ) * Real.exp n)) ≤
      Real.exp ((p + C) ^ C) := by
    have h1 : 1 ≤ Real.exp d := Real.one_le_exp hd
    calc
      _ = Real.exp d * Real.exp n * (1 + Real.exp d * s) := by ring
      _ ≤ Real.exp d * Real.exp n * (Real.exp d * (1 + s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = (Real.exp d * Real.exp d * Real.exp n) * (s + 1) := by ring
      _ ≤ (Real.exp d * Real.exp d * Real.exp n) * Real.exp (s + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (s + 1 : ℝ)]) (by positivity)
      _ = Real.exp (2 * d + n + (s + 1 : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hremCap
  obtain ⟨m, hm, hmp, hlm, hlogGrid, hadGrid⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hgridCap), hlm, ?_⟩
  intro T hT A B hA hB hAbound hBgrid κ S R small rational hS hR hsmall hrational hSbound hRgrid hsmallBound hrationalGrid
  have hg := hgraded.baseChange b ω
  have hAi : A⁻¹.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ : σ => 1) :=
    (gradedPolynomialSubmodule (b.baseChange ℝ) ω _).neg_mem hA
  have hAa := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) A.coord hA
  have hAia := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) A⁻¹.coord hAi
  have hBa := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) B.coord hB
  have hAib : CoefficientBound (b.baseChange ℝ) T (Real.exp n) A⁻¹.coord :=
    CoefficientBound.neg _ _ hAbound
  have hoperations := hbound F b ω hF H p hH hp hι hσ hHp hc T hT
  have hYA (i : σ) := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule
    (b.baseChange ℝ) ω hg i A hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have hslow := hoperations.1 A⁻¹ hAia hAib (Real.exp n) (Real.exp_nonneg _) (S k)
      (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hS k)) (hSbound k)
    have hfactor : Real.exp d * Real.exp n ≤ Real.exp ((p + C) ^ C) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hliftCap
    exact ⟨CoefficientBound.mono _ T hT hslow hfactor,
      hadGrid B (R k) hBa (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hR k)) hBgrid (hRgrid k)⟩
  · intro i
    have hyBound := hoperations.2 A hAa hAbound i
    have hdiff := CoefficientBound.sub (b.baseChange ℝ) T (hsmallBound i) hyBound
    have hdiffGrade := (shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ : σ => 1) 1).sub_mem
      (hsmall i) (hYA i)
    have hslow := hoperations.1 A⁻¹ hAia hAib
      (Real.exp n / T i + Real.exp d * ((s : ℝ) * Real.exp n / T i)) (by have hTi := hT i; positivity)
      (small i - formalLogDerivative i A)
      (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ hdiffGrade) hdiff
    have hfactor : Real.exp d * (Real.exp n / T i + Real.exp d * ((s : ℝ) * Real.exp n / T i)) ≤
        Real.exp ((p + C) ^ C) / T i := by
      calc
        _ = (Real.exp d * (Real.exp n + Real.exp d * ((s : ℝ) * Real.exp n))) / T i := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hslowCap (hT i).le
    exact ⟨CoefficientBound.mono _ T hT hslow hfactor,
      CoefficientGrid.sub _ m
        (hadGrid B (rational i) hBa (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hrational i))
          hBgrid (hrationalGrid i)) (hlogGrid B hBa hBgrid i)⟩
  · intro k
    exact ⟨dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω hg _ 1 A⁻¹ (S k) hAi (hS k),
      dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω hg _ 1 B (R k) hB (hR k)⟩
  · intro i
    exact polynomial_derivative_removal_preserves_shifted_grading (b.baseChange ℝ) ω hg i A B
      (small i) (rational i) hA hB (hsmall i) (hrational i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_controlled_current_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hrows : (Fintype.card ι : ℝ) ≤ p)
    (_hcols : (Fintype.card ν : ℝ) ≤ p) (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (_hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (_hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (_hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (_hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l)
    {κ : Type*} (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ → ℝ ⊗[ℚ] L)
    (_hS : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1)
    (_hR : ∀ t, R t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1)
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSres : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hRres : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hSbound : ∀ t, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S t))
    (_hRgrid : ∀ t, CoefficientGrid (b.baseChange ℝ) l (R t))
    (_hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (_hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P'
          (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
        (∀ t α, coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ t, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (dualAdjoint A⁻¹ (S t)) ∧
          CoefficientGrid (b.baseChange ℝ) n (dualAdjoint B (R t)) ∧
          dualAdjoint A⁻¹ (S t) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1 ∧
          dualAdjoint B (R t) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1) ∧
        ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) := by
  obtain ⟨D, _, hstage⟩ := exists_uniform_formal_current_layer_step
  obtain ⟨E, _, hremove⟩ := exists_formal_derivative_removal_control s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D + (Q + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro L μ ι ν σ _ _ _ _ _ _ F b w hF Vsource V hgraded hs U K hUV hV e f j H J Qheight l
    hj hE hEU hH hl hA he hf hstructure p M hp hM hambient hrows hcols hvariables hjp
    hHp hJp hQp hlp hMp T hT P hPU hPgraded hPE hK hlower hbracket small rational extra
    hsmall hrational hextra hsystem hSgraded hRgraded hslow hgrid κ S R k hS hR hSR hSres hRres
    hSbound hRgrid hsmallBound hrationalGrid
  let d := (p + D) ^ D
  let q := p + d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hqE : 0 ≤ (q + E) ^ E := by positivity
  have htotal : d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
    simpa [B, Q, q, d, Polynomial.eval₂_pow] using hCbound p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hremCap : (q + E) ^ E ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  obtain ⟨n₀, A, Bcorr, hn₀, hn₀bound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩ :=
    hstage F b w hF hgraded hs U K hUV hV e f hj hE hEU hH hl hA he hf hp hM
      hambient hrows hcols hvariables hjp hHp hJp hQp hlp hMp T hTD
      P hPU hPgraded hPE hK hlower hbracket small rational extra hsmall hrational hextra
      hsystem hSgraded hRgraded hslow hgrid
  let Lden := l * n₀
  have hLden : 0 < Lden := Nat.mul_pos hl hn₀
  have hLbound : (Lden : ℝ) ≤ Real.exp q := by
    calc
      _ = (l : ℝ) * (n₀ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp p * Real.exp d := mul_le_mul hlp hn₀bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  obtain ⟨m, hm, hmbound, hLm, hcontrol⟩ := hremove F b w hF hgraded H q hH hq
    (hambient.trans hpq) (hvariables.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    hstructure Lden hLden hLbound
  have hlL : l ∣ Lden := dvd_mul_right l n₀
  have hnL : n₀ ∣ Lden := dvd_mul_left n₀ l
  have hAg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j A.coord hAhom (fun α => hE _ (hAB α).1)
  have hBg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j Bcorr.coord hBhom (fun α => hE _ (hAB α).2)
  have hAraw : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) A.coord).mpr hAnorm
  have hAinput : CoefficientBound (b.baseChange ℝ) T (Real.exp ((q + 2) ^ 1)) A.coord := by
    apply CoefficientBound.mono _ T hTpos hAraw
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    dsimp [q]
    linarith
  have hBinput : CoefficientGrid (b.baseChange ℝ) Lden Bcorr.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hn₀ hnL (hBgrid α)
  have hinputCap : Real.exp p ≤ Real.exp ((q + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  obtain ⟨hboundLifts, hboundDerivative, hshiftLifts, _⟩ := hcontrol T hTpos A Bcorr hAg hBg hAinput hBinput
    S R small rational hS hR hSgraded hRgraded
    (fun t => CoefficientBound.mono _ T hTpos (hSbound t) hinputCap)
    (fun t α => realDenominatorGrid_subset_of_dvd hl hlL (hRgrid t α))
    (fun i => CoefficientBound.mono _ T hTpos (hsmallBound i)
      (div_le_div_of_nonneg_right hinputCap (hTpos i).le))
    (fun i α => realDenominatorGrid_subset_of_dvd hl hlL (hrationalGrid i α))
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hE _ (hAB α).1]
    exact F.realGradeProjection_mem_layer b w hF j _
  have hBlayer : ∀ α, coefficients Bcorr.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hE _ (hAB α).2]
    exact F.realGradeProjection_mem_layer b w hF j _
  have hWiff (x : ℝ ⊗[ℚ] L) :
      x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔ F.realification.layer (j + 1) ↔
        x ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    change x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔
      (F.realLayer (j + 1)).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hkeep := F.formal_current_layer_correction_preserves_lifts_mod hs Uq
    ((V.baseChange ℝ).restrictScalars ℚ) hUV j P A Bcorr
    (fun α => hEU _ (hAB α).1) hAlayer hBlayer S R k hSR
    (fun t α => (hWiff _).mpr (hSres t α)) (fun t α => (hWiff _).mpr (hRres t α))
  have hfinalCap : Real.exp ((q + E) ^ E) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hremCap
  refine ⟨m, A, Bcorr, hm, hmbound.trans hfinalCap, hAB, hAhom, hBhom, ?_, ?_,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra, hkeep.1, ?_, ?_, ?_⟩
  · intro α
    exact (hAnorm α).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdCap)
      (monomialScale_pos T hTpos α).le)
  · intro α
    exact realDenominatorGrid_subset_of_dvd hn₀ (dvd_trans hnL hLm) (hBgrid α)
  · intro t α
    exact ⟨(hWiff _).mp (hkeep.2 t α).1, (hWiff _).mp (hkeep.2 t α).2⟩
  · intro t
    exact ⟨CoefficientBound.mono _ T hTpos (hboundLifts t).1 hfinalCap,
      (hboundLifts t).2, (hshiftLifts t).1, (hshiftLifts t).2⟩
  · intro i
    exact ⟨CoefficientBound.mono _ T hTpos (hboundDerivative i).1
      (div_le_div_of_nonneg_right hfinalCap (hTpos i).le), (hboundDerivative i).2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
