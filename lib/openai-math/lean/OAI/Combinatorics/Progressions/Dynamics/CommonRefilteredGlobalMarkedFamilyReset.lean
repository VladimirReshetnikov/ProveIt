import OAI.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
import OAI.Combinatorics.Progressions.Geometry.GlobalMarkedNativeChartResetConditions
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinateFreezeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_terminal_native_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l : ℕ) (pMap pNative : ℝ), 1 ≤ H → 0 < l → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ (side : σ → ℝ), (∀ i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side i) →
    ∀ (q : ℝ), Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      G.PolynomialSlowBound c (fun _ : σ => 1) side (Real.exp ((pNative + 2) ^ a)) EF →
      G.PolynomialRationalGrid c (fun _ : σ => 1) mMap RF →
      (G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) (EF⁻¹ * X * RF⁻¹)).coord ∈
        realificationLieSubalgebra (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))) →
      coefficients ((EF⁻¹ * X * RF⁻¹).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (W.map (F.associatedGradedMap G φ hφ)) 1 →
    ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g = X →
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e = EF ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r = RF ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle = EF⁻¹ * X * RF⁻¹ ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) side
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        native.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t native) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t middle := by
  obtain ⟨Ccompare, hCcompare, hcompare⟩ := exists_common_refiltered_terminal_discrepancies s a
  obtain ⟨Cf, Cnative, hCf, hCnative, hnative⟩ :=
    exists_controlled_prescribed_marked_native_factorizations s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l pMap pNative hH hl hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  obtain ⟨mMap, hmMap, hmMapBound, hlmMap, hdiscrepancy⟩ :=
    hcompare (χ := χ) F G b ω hF c ν hG φ hφ H l pMap hH hl hpMap hentries hsrc htgt hHmap hlmap
  obtain ⟨m, hm, hmp, hmMapm, hreset⟩ := hnative F G φ hφ b ω hF c ν hG
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hsurj bk W v hW hvspan H mMap pNative
    hH hmMap hpNative hι hκ hξ hμ hσ hHp (hmMapBound.trans hmabsorb)
    hb hc hkernel hentries hv
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro side hside q hq hmapslow X EF RF hEF hRF hterminal hconstant g hg hfactor
  have hsidePos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨E, P, R, hprod, hP, hE, hR, hdiff⟩ :=
    hdiscrepancy H pNative hH hpNative hκ hσ hχ hHp hmabsorb hc
      side hside q hmapslow W vg hvgspan hvg g hfactor
  have hterminal' :
      ((G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) EF)⁻¹ *
        G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) *
        (G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) RF)⁻¹).coord ∈
        realificationLieSubalgebra (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [map_mul, map_inv, hg] using hterminal
  obtain ⟨hleft, hright⟩ := hdiff _ _ hterminal'
    (G.polynomialSlowBound_symbol c ν hG (fun _ : σ => 1) side _ EF hEF)
    (G.polynomialRationalGrid_symbol c ν hG (fun _ : σ => 1) mMap RF hRF)
  exact hreset side hsidePos X EF RF hEF hRF hconstant g hg E P R hprod hP
    (F.symbolSlowBound_mono b ω hF (fun _ : σ => 1) side hsidePos hq E hE)
    (F.symbolRationalGrid_mono b ω hF (fun _ : σ => 1) hl hlmMap R hR) hleft hright

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra

theorem exists_common_refiltered_globalMarked_native_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l : ℕ) (pMap pNative : ℝ), 1 ≤ H → 0 < l → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ (side : σ → ℝ), (∀ i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side i) →
    ∀ (q : ℝ), Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
    ∀ {α : Type*} (w : α → ℕ) (β : α → MvPolynomial α ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
      (marked : (G.realification.adaptedPolynomialFiltration w).Group)
      (E R : G.RealPolynomialSymbolGroup w)
      (A : GlobalMarkedNativeFactors G c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))
        (G.weightedAdaptedRealChartHom w w β hβ marked) E R)
      (γ : α → MvPolynomial σ ℤ)
      (hγ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (γ i) ∈
        weightedSupportLE (fun _ : σ => 1) (w i)),
      (∀ t : σ → ℝ,
        (fun i => MvPolynomial.eval
          (fun j => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ j))) (β i)) =
        (fun i => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ i)))) →
      G.PolynomialSlowBound c (fun _ : σ => 1) side (Real.exp ((pNative + 2) ^ a))
        (G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.left) →
      G.PolynomialRationalGrid c w l A.right →
    ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ marked →
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.left ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.right ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.middle ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) side
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        native.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t native) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t middle := by
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_terminal_native_reset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l pMap pNative hH hl hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  obtain ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, hrun⟩ :=
    hreset F G φ hφ b ω hF c ν hG hsurj bk W v hW hvspan vg hvgspan
      H l pMap pNative hH hl hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
      hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro side hside q hq hmapslow α w β hβ marked E R A γ hγ hfixed hslow hgrid g hg hcommon
  let γR := fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)
  let pull := G.weightedAdaptedRealChartHom w (fun _ : σ => 1) γR hγ
  have hlocalGrid : G.PolynomialRationalGrid c (fun _ : σ => 1) mMap (pull A.right) :=
    G.polynomialRationalGrid_of_dvd c (fun _ : σ => 1) hl hlmMap _
      (G.polynomialRationalGrid_integerChart c w (fun _ : σ => 1) γ hγ l A.right hgrid)
  have hconditions := A.fixed_chart_native_conditions γR hγ hfixed
  have hresidual := A.fixed_chart_residual_eq γR hγ hfixed
  obtain ⟨e, middle, r, native, hprod, he, hr, hmid, heSlow, hrGrid, hlog, hvalues⟩ :=
    hrun side hside q hq hmapslow (pull marked) (pull A.left) (pull A.right)
      hslow hlocalGrid hconditions.1 hconditions.2 g hg hcommon
  exact ⟨e, middle, r, native, hprod, he, hr, hmid.trans hresidual,
    heSlow, hrGrid, hlog, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

theorem HasCommonRefilteredOrbitFactors.of_dvd
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (side : σ → ℝ) (q : ℝ) {l n : ℕ} (hl : 0 < l) (hln : l ∣ n)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q n W g := by
  obtain ⟨e, middle, r, hprod, hfast, he, hr, he0, hr0, hmiddle0⟩ := h
  exact ⟨e, middle, r, hprod, hfast, he,
    F.polynomialRationalGrid_of_dvd b (fun _ : σ => 1) hl hln r hr,
    he0, hr0, hmiddle0⟩

theorem exists_common_refiltered_globalMarked_family_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l nFinal : ℕ) (pMap pNative : ℝ),
      1 ≤ H → 0 < l → 0 < nFinal → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → ((l * nFinal : ℕ) : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l * nFinal ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ {Ω α : Type*} (w : α → ℕ) (β : α → MvPolynomial α ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
      (marked : (G.realification.adaptedPolynomialFiltration w).Group)
      (E R : G.RealPolynomialSymbolGroup w)
      (A : GlobalMarkedNativeFactors G c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))
        (G.weightedAdaptedRealChartHom w w β hβ marked) E R),
      G.PolynomialRationalGrid c w nFinal A.right →
    ∀ (side : Ω → σ → ℝ) (q : Ω → ℝ)
      (γ : Ω → α → MvPolynomial σ ℤ)
      (hγ : ∀ z i, MvPolynomial.map (Int.castRingHom ℝ) (γ z i) ∈
        weightedSupportLE (fun _ : σ => 1) (w i)),
      (∀ z i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side z i) →
      (∀ z, Real.exp (q z) ≤ Real.exp ((pNative + 2) ^ a)) →
      (∀ z, Real.exp ((pMap + 2) ^ 3 + q z) ≤ Real.exp ((pNative + 2) ^ a)) →
      (∀ z, ∀ t : σ → ℝ,
        (fun i => MvPolynomial.eval
          (fun j => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ z j))) (β i)) =
        (fun i => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ z i)))) →
      (∀ z, G.PolynomialSlowBound c (fun _ : σ => 1) (side z) (Real.exp ((pNative + 2) ^ a))
        (G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.left)) →
    ∀ g : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ z, F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (g z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) marked) →
      (∀ z, F.HasCommonRefilteredOrbitFactors b ω hF (side z) (q z) l W (g z)) →
    ∃ (e middle r : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : Ω → (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      ∀ z,
      e z * middle z * r z = g z ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (e z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.left ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (r z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.right ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (middle z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.middle ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) (side z)
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) (e z) ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m (r z) ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (native z).log = ((middle z).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t (native z)) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t (middle z) := by
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_globalMarked_native_reset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  have hwide : 0 < l * nFinal := Nat.mul_pos hl hnFinal
  obtain ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, hrun⟩ :=
    hreset F G φ hφ b ω hF c ν hG hsurj bk W v hW hvspan vg hvgspan
      H (l * nFinal) pMap pNative hH hwide hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
      hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro Ω α w β hβ marked E R A hgrid side q γ hγ hside hq hmapslow hfixed hslow g hg hcommon
  have hglobalGrid : G.PolynomialRationalGrid c w (l * nFinal) A.right :=
    G.polynomialRationalGrid_of_dvd c w hnFinal (dvd_mul_left nFinal l) A.right hgrid
  have hfamily (z : Ω) := hrun (side z) (hside z) (q z) (hq z) (hmapslow z)
    w β hβ marked E R A (γ z) (hγ z) (hfixed z) (hslow z) hglobalGrid (g z) (hg z)
    (HasCommonRefilteredOrbitFactors.of_dvd F b ω hF (side z) (q z) hl
      (dvd_mul_right l nFinal) W (g z) (hcommon z))
  classical
  choose e middle r native hproperties using hfamily
  exact ⟨e, middle, r, native, hproperties⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
