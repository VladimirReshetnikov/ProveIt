import OAI.Combinatorics.Progressions.Dynamics.FilteredSectionSingleDenominatorBudget
import OAI.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_prescribed_real_polynomial_lift
    {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ l ∣ m ∧
      ∀ (x : F.RealPolynomialSymbolGroup w)
        (q : (G.realification.adaptedPolynomialFiltration w).Group),
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x.coord =
        (G.realPolynomialSymbolHom c τ hG w q).coord →
      ∃ z : (F.realification.adaptedPolynomialFiltration w).Group,
        F.realPolynomialSymbolHom b ω hF w z = x ∧
        F.realPolynomialGroupMap G φ hφ w z = q ∧
        (∀ (a : ℕ) (T : σ → ℝ), (∀ i, 0 < T i) →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) x →
          CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) q.coord.val →
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) z.coord.val) ∧
        (F.SymbolRationalGrid b ω hF w l x → CoefficientGrid (c.baseChange ℝ) l q.coord.val →
          CoefficientGrid (b.baseChange ℝ) m z.coord.val) := by
  classical
  obtain ⟨S, hS, hSlayer, hheight⟩ := F.exists_bounded_filtered_section G b ω hF c τ hG
    φ.toLinearMap hsurj hH hentries
  have hφm : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hentries i j
  have hSm : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j)
      (rationalKernelHeight (Fintype.card κ) H) := by
    intro i j
    simpa only [LinearMap.toMatrix_apply] using hheight i j
  let m := matrixDenominator (LinearMap.toMatrix c b S) *
    matrixDenominator (LinearMap.toMatrix b c φ.toLinearMap) * l
  obtain ⟨hm, hlm, _⟩ := sectionCorrectedPolynomial_denominator_bounds b c φ.toLinearMap S hφm hSm hl
  refine ⟨m, hm, filtered_section_pair_denominator_le_exp
    (LinearMap.toMatrix b c φ.toLinearMap) (LinearMap.toMatrix c b S) l hp hι hκ hHp hφm hSm hlp,
    hlm, ?_⟩
  intro x q hcompat
  obtain ⟨z, hz, hsymbol, hmarked⟩ := F.sectionCorrectedPolynomial_prescribed_symbol G φ hφ
    b ω hF c τ hG w S hS hSlayer x.coord q.coord hcompat
  refine ⟨⟨z⟩, NilpotentLieBCHGroup.ext hsymbol, NilpotentLieBCHGroup.ext hmarked, ?_, ?_⟩
  · intro a T hT hx hq
    change CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) z.val
    rw [hz]
    have hx' : CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a))
        (F.realSymbolRepresentative b ω hF w x.coord) :=
      F.realSymbolRepresentative_slow_coefficients b ω hF w T hT (Real.exp_nonneg _) x hx
    have hout := sectionCorrectedPolynomial_coefficientBound b c φ.toLinearMap S hφm hSm
      (F.realSymbolRepresentative b ω hF w x.coord) q.coord.val T hT
      (Real.exp_nonneg _) (Real.exp_nonneg _) hx' hq
    exact hout.mono _ T hT
      (filtered_section_coefficient_loss_le_exp (Fintype.card ι) (Fintype.card κ) H a hp hι hκ hHp)
  · intro hx hq
    change CoefficientGrid (b.baseChange ℝ) m z.val
    rw [hz]
    have hx' : CoefficientGrid (b.baseChange ℝ) l
        (F.realSymbolRepresentative b ω hF w x.coord) := by
      obtain ⟨v, hv⟩ := F.realSymbolRepresentative_rational_coefficients b ω hF w l x hx
      intro α
      exact ⟨fun i => v (α, i), funext (fun i => congrFun hv (α, i))⟩
    exact sectionCorrectedPolynomial_coefficientGrid b c φ.toLinearMap S
      (F.realSymbolRepresentative b ω hF w x.coord) q.coord.val hl hx' hq

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_polynomial_factorization
    {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ l ∣ m ∧
      ∀ (a : ℕ) (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : F.RealPolynomialSymbolGroup w),
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      ∀ EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
        (G.realPolynomialSymbolHom c τ hG w EF).coord →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
        (G.realPolynomialSymbolHom c τ hG w RF).coord →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) EF.coord.val →
      F.SymbolRationalGrid b ω hF w l R →
      CoefficientGrid (c.baseChange ℝ) l RF.coord.val →
      ∃ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        e * middle * r = g ∧
        F.realPolynomialSymbolHom b ω hF w e = E ∧
        F.realPolynomialSymbolHom b ω hF w middle = P ∧
        F.realPolynomialSymbolHom b ω hF w r = R ∧
        F.realPolynomialGroupMap G φ hφ w e = EF ∧
        F.realPolynomialGroupMap G φ hφ w r = RF ∧
        F.realPolynomialGroupMap G φ hφ w middle =
          EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) e.coord.val ∧
        CoefficientGrid (b.baseChange ℝ) m r.coord.val := by
  obtain ⟨m, hm, hmp, hlm, hlift⟩ := F.exists_controlled_prescribed_real_polynomial_lift
    G φ hφ b ω hF c τ hG w hsurj hH hl hentries hp hι hκ hHp hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro a T hT g E P R hprod EF RF hE hR hEslow hEFbound hRgrid hRFgrid
  obtain ⟨e, he, heF, hebound, _⟩ := hlift E EF hE
  obtain ⟨r, hr, hrF, _, hrgrid⟩ := hlift R RF hR
  refine ⟨e, e⁻¹ * g * r⁻¹, r, by group, he, ?_, hr, heF, hrF, ?_,
    hebound a T hT hEslow hEFbound, hrgrid hRgrid hRFgrid⟩
  · rw [map_mul, map_mul, map_inv, map_inv, he, hr, ← hprod]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, heF, hrF]

end Erdos3.NilpotentLieFiltration

end

end OAI
