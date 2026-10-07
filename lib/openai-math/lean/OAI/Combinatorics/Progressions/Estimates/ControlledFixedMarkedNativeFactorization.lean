import OAI.Combinatorics.Progressions.Estimates.FullMarkedNativeFactorization
import OAI.Combinatorics.Progressions.Polynomial.ControlledMarkedPolynomialFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

def markedNativeLiftInput (p : ℝ) : ℝ := (p + 2) ^ 11 + p

theorem exists_controlled_marked_native_factorization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((markedNativeLiftInput p + C) ^ C) ∧ l ∣ m ∧
    ∀ (U : LieSubalgebra ℚ F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
      (E P R : F.RealPolynomialSymbolGroup w),
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
    ∀ EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
        (G.realPolynomialSymbolHom c τ hG w EF).coord →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
        (G.realPolynomialSymbolHom c τ hG w RF).coord →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) EF.coord.val →
      F.SymbolRationalGrid b ω hF w l R →
      CoefficientGrid (c.baseChange ℝ) l RF.coord.val →
      coefficients ((EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialSymbolHom b ω hF w e = E ∧
      F.realPolynomialSymbolHom b ω hF w middle = P ∧
      F.realPolynomialSymbolHom b ω hF w r = R ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w middle =
        EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
      F.PolynomialSlowBound b w T (Real.exp ((markedNativeLiftInput p + C) ^ C)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
          F.adaptedPolynomialRealValueHom w z middle := by
  obtain ⟨C, hC, hnormalize⟩ := exists_controlled_marked_kernel_normalization s (a + 12)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ξ L M _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk H l p hH hl hp hι hκ hξ hσ hHp hlp hbracket hkernel hentries
  obtain ⟨m₀, hm₀, hm₀p, hlm₀, hlift⟩ := F.exists_controlled_marked_polynomial_factorization
    G φ hφ b ω hF c τ hG w hsurj hH hl hentries hp hι hκ hHp hlp
  let B := markedNativeLiftInput p
  have hpB : p ≤ B := by
    dsimp [B, markedNativeLiftInput]
    exact le_add_of_nonneg_left (by positivity)
  have hB : 0 ≤ B := hp.trans hpB
  have hm₀B : (m₀ : ℝ) ≤ Real.exp B := hm₀p.trans (Real.exp_le_exp.mpr
    (by dsimp [B, markedNativeLiftInput]; exact le_add_of_nonneg_right hp))
  obtain ⟨m, hm, hmp, hm₀m, hnorm⟩ := hnormalize F G φ hφ b ω hF w hw bk H m₀ B
    hH hm₀ hB (hι.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) hm₀B hbracket hkernel
  refine ⟨m, hm, hmp, hlm₀.trans hm₀m, ?_⟩
  intro U hU T hT g E P R hprod hP EF RF hE hR hEslow hEF hRgrid hRF hconstant
  obtain ⟨e₀, middle₀, r₀, hprod₀, he₀, hp₀, hr₀, heF₀, hrF₀, hpF₀,
    hebound₀, hrgrid₀⟩ := hlift a T hT g E P R hprod EF RF hE hR hEslow hEF hRgrid hRF
  have hebound : F.PolynomialSlowBound b w T (Real.exp ((B + 2) ^ (a + 12))) e₀ :=
    F.polynomialSlowBound_mono b w T hT
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) _)) e₀ hebound₀
  have hrgrid : F.PolynomialRationalGrid b w m₀ r₀ := by
    choose v hv using hrgrid₀
    exact ⟨fun z => v z.1 z.2, funext (fun z => congrFun (hv z.1) z.2)⟩
  have hpc : realificationLieHom φ
      (coefficients (middle₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
      ((F.gradedRefiltrationLayer U 1).map φ.toLinearMap).baseChange ℝ := by
    rw [F.gradedRefiltrationLayer_map G b ω hF c τ hG φ hφ U hU hsurj]
    have hlog := congrArg (fun z => coefficients
      (z.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0) hpF₀
    rw [F.realPolynomialGroupMap_log, coefficients_map] at hlog
    change realificationLieHom φ (coefficients
      (middle₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) = _ at hlog
    rwa [hlog]
  obtain ⟨u, v, e, middle, r, _, _, _, _, hproduct, hEs, hPs, hRs,
    hEm, hPm, hRm, hconst, heslow, hrgrid⟩ := hnorm (F.gradedRefiltrationLayer U 1)
      (F.layer_succ_le_gradedRefiltrationLayer U 1) T hT e₀ middle₀ r₀ hebound hrgrid hpc
  have hmiddle : F.realPolynomialSymbolHom b ω hF w middle = P := hPs.trans hp₀
  have hvalues := (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U
    (F.realPolynomialSymbolHom b ω hF w middle).coord).mp
      (by rw [hmiddle]; exact hP)
  obtain ⟨q, hq, hqvalues⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant U
    b ω hF w hw middle.coord hconst hvalues
  exact ⟨e, middle, r, q, hproduct.trans hprod₀, hEs.trans he₀, hmiddle, hRs.trans hr₀,
    hEm.trans heF₀, hRm.trans hrF₀, hPm.trans hpF₀, heslow, hrgrid, hq, hqvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

def fixedMarkedNativeInput (a C : ℕ) (p : ℝ) : ℝ :=
  (p + C) ^ C + (p + 2) ^ a + p

theorem exists_controlled_fixed_marked_native_factorizations (s a : ℕ) :
    ∃ C₀ C₁ : ℕ, 2 ≤ C₀ ∧ 2 ≤ C₁ ∧
    ∀ {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput (fixedMarkedNativeInput a C₀ p) + C₁) ^ C₁) ∧
      l ∣ m ∧
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      G.PolynomialRationalGrid c w l RF →
    ∃ (u : ℝ ⊗[ℚ] M) (v : M)
      (EF' RF' : (G.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (c.baseChange ℝ).repr u i ∧ (c.baseChange ℝ).repr u i < 1) ∧
      (∀ i, ∃ z : ℤ, c.repr v i = z) ∧
      EF' = EF * G.realification.adaptedConstantGroupHom w ⟨u⟩ ∧
      RF' = G.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * RF ∧
      G.realPolynomialSymbolHom c τ hG w EF' = G.realPolynomialSymbolHom c τ hG w EF ∧
      G.realPolynomialSymbolHom c τ hG w RF' = G.realPolynomialSymbolHom c τ hG w RF ∧
      G.PolynomialSlowBound c w T (Real.exp ((p + C₀) ^ C₀)) EF' ∧
      G.PolynomialRationalGrid c w m RF' ∧
    ∀ (U : LieSubalgebra ℚ F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group),
      F.realPolynomialGroupMap G φ hφ w g = X →
    ∀ E P R : F.RealPolynomialSymbolGroup w,
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
        (G.realPolynomialSymbolHom c τ hG w EF).coord →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
        (G.realPolynomialSymbolHom c τ hG w RF).coord →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolRationalGrid b ω hF w l R →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialSymbolHom b ω hF w e = E ∧
      F.realPolynomialSymbolHom b ω hF w middle = P ∧
      F.realPolynomialSymbolHom b ω hF w r = R ∧
      F.realPolynomialGroupMap G φ hφ w e = EF' ∧
      F.realPolynomialGroupMap G φ hφ w r = RF' ∧
      F.realPolynomialGroupMap G φ hφ w middle = EF'⁻¹ * X * RF'⁻¹ ∧
      F.PolynomialSlowBound b w T
        (Real.exp ((markedNativeLiftInput (fixedMarkedNativeInput a C₀ p) + C₁) ^ C₁)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
          F.adaptedPolynomialRealValueHom w z middle := by
  obtain ⟨C₀, hC₀, htarget⟩ := exists_controlled_marked_target_normalization s a
  obtain ⟨C₁, hC₁, hnative⟩ := exists_controlled_marked_native_factorization s 1
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro σ ι κ ξ L M _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk H l p hH hl hp hι hκ hξ hσ hHp hlp hbracket htargetBracket hkernel hentries
  obtain ⟨n, hn, hnp, hln, hnorm⟩ :=
    htarget G c τ hG w hw H l p hH hl hp hκ hσ hHp hlp htargetBracket
  let B := fixedMarkedNativeInput a C₀ p
  have htarget0 : 0 ≤ (p + C₀) ^ C₀ := by positivity
  have hslow0 : 0 ≤ (p + 2) ^ a := by positivity
  have hpB : p ≤ B := by dsimp [B, fixedMarkedNativeInput]; linarith
  have htargetB : (p + C₀) ^ C₀ ≤ B := by dsimp [B, fixedMarkedNativeInput]; linarith
  have hslowB : (p + 2) ^ a ≤ B := by dsimp [B, fixedMarkedNativeInput]; linarith
  have hB : 0 ≤ B := hp.trans hpB
  obtain ⟨m, hm, hmp, hnm, hfactor⟩ := hnative F G φ hφ b ω hF c τ hG w hw hsurj
    bk H n B hH hn hB (hι.trans hpB) (hκ.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) (hnp.trans (Real.exp_le_exp.mpr htargetB))
    hbracket hkernel hentries
  refine ⟨m, hm, hmp, hln.trans hnm, ?_⟩
  intro T hT X EF RF hEF hRF
  obtain ⟨u, v, EF', PH', RF', hu, hv, hEF', hRF', hproduct, hESym, _, hRSym,
    hconstant, hEFslow, hRFgrid⟩ := hnorm T hT EF (EF⁻¹ * X * RF⁻¹) RF hEF hRF
  have hproduct' : EF' * PH' * RF' = X := hproduct.trans (by group)
  have hmiddle : PH' = EF'⁻¹ * X * RF'⁻¹ := by
    calc
      PH' = EF'⁻¹ * (EF' * PH' * RF') * RF'⁻¹ := by group
      _ = _ := by rw [hproduct']
  refine ⟨u, v, EF', RF', hu, hv, hEF', hRF', hESym, hRSym, hEFslow,
    G.polynomialRationalGrid_of_dvd c w hn hnm RF' hRFgrid, ?_⟩
  intro U hU g hg E P R hprod hP hE hR hEslow hRgrid
  have hfirst : coefficients ((EF'⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF'⁻¹).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 := by
    rw [hg, ← hmiddle]
    exact Submodule.baseChange_mono ℝ
      (G.layer_succ_le_gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1) hconstant
  have hEslow' : F.SymbolSlowBound b ω hF w T (Real.exp ((B + 2) ^ 1)) E :=
    F.symbolSlowBound_mono b ω hF w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hslowB.trans (by linarith))) E hEslow
  have hEFslow' : CoefficientBound (c.baseChange ℝ) T (Real.exp ((B + 2) ^ 1)) EF'.coord.val :=
    G.polynomialSlowBound_mono c w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using htargetB.trans (by linarith))) EF' hEFslow
  have hRFgrid' : CoefficientGrid (c.baseChange ℝ) n RF'.coord.val := by
    obtain ⟨z, hz⟩ := hRFgrid
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  obtain ⟨e, middle, r, q, hprod', he, hmid, hr, heF, hrF, hmidF, heslow,
    hrgrid, hq, hvalues⟩ := hfactor U hU T hT g E P R hprod hP EF' RF'
      (hE.trans (congrArg NilpotentLieBCHGroup.coord hESym).symm)
      (hR.trans (congrArg NilpotentLieBCHGroup.coord hRSym).symm)
      hEslow' hEFslow' (F.symbolRationalGrid_mono b ω hF w hl hln R hRgrid) hRFgrid' hfirst
  exact ⟨e, middle, r, q, hprod', he, hmid, hr, heF, hrF, hmidF.trans (by rw [hg]),
    heslow, hrgrid, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
