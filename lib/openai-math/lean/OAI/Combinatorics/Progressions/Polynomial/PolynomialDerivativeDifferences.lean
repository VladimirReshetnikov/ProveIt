import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_real_adapted_dual_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          ∀ h : σ → ℤ, F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) m
            (F.realAdaptedLogDerivative (fun i => (h i : ℚ)) x)) ∧
        (∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
          (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l g.coord →
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) m (dualAdjoint g x)) := by
  have hgridExists := exists_real_dual_operation_grid s
  obtain ⟨D, _, hgrid⟩ := hgridExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let B : Polynomial ℕ := (Q + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  let : Fintype (AdaptedBasisIndex (fun _ : σ => 1) ω) :=
    adaptedBasisIndexFintype (fun _ => 1) ω s (by simp) (F.adaptedBasis_weight_le_step b ω hF)
  let q := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (s + 2))).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le (fun _ : σ => 1) ω s (by simp)
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hfinal : (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hdata := hgrid (F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)) H q
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot
    hH hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hF (fun _ => 1) hH hc)
    l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_, ?_⟩
  · intro x hx h
    have hout := hlog (F.realAdaptedPolynomialJet (fun i => (h i : ℚ)) x)
      (by simpa only [F.realAdaptedPolynomialJet_base, RealAdaptedCoefficientGrid,
        Basis.equivFun_apply] using hx)
      (by simpa only [F.realAdaptedPolynomialJet_tangent, RealAdaptedCoefficientGrid,
        Basis.equivFun_apply] using F.realAdaptedDirectionalDerivative_grid b ω hF l x hx h)
    simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply, realAdaptedLogDerivative] using hout
  · intro g x hg hx
    have hout := had g x
      (by simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hg)
      (by simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hx)
    simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hout

theorem realAdaptedAdjoint_tensor {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedPolynomialTensor w (dualAdjoint g x) =
      dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialTensor w x) := by
  let φ := F.realAdaptedPolynomialTensor w
  exact dualLinearLift_adjoint (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)) φ φ.toLinearMap
    (fun u v _ => φ.map_lie u v) g x (by trivial)

theorem exists_polynomial_dual_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
          F.PolynomialRationalGrid b (fun _ => 1) l g →
          ∀ h : σ → ℤ, F.PolynomialRationalGrid b (fun _ => 1) m
            ⟨F.realification.adaptedLogDerivative (fun i => (h i : ℚ)) g.coord⟩) ∧
        (∀ g r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
          F.PolynomialRationalGrid b (fun _ => 1) l g →
          F.PolynomialRationalGrid b (fun _ => 1) l r →
          F.PolynomialRationalGrid b (fun _ => 1) m ⟨dualAdjoint g r.coord⟩) := by
  have hgridExists := exists_real_adapted_dual_grid s
  obtain ⟨C, hC, hgrid⟩ := hgridExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  have hdata := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro g hg h
    let q := F.realAdaptedPolynomialGroupLift (fun _ : σ => 1) b ω hF g
    have hqg := F.realAdaptedPolynomialGroupHom_lift (fun _ : σ => 1) b ω hF g
    have hq := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) l q).mpr
      (by simpa only [q, hqg] using hg)
    have hout := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) m
      (⟨F.realAdaptedLogDerivative (fun i => (h i : ℚ)) q.coord⟩ :
        F.RealAdaptedPolynomialGroup (fun _ => 1))).mp (hlog q.coord hq h)
    have heq : F.realAdaptedPolynomialGroupHom (fun _ => 1)
        (⟨F.realAdaptedLogDerivative (fun i => (h i : ℚ)) q.coord⟩ :
          F.RealAdaptedPolynomialGroup (fun _ => 1)) =
        ⟨F.realification.adaptedLogDerivative (fun i => (h i : ℚ)) g.coord⟩ := by
      apply NilpotentLieBCHGroup.ext
      change F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedLogDerivative _ q.coord) = _
      rw [F.realAdaptedLogDerivative_tensor]
      exact congrArg (F.realification.adaptedLogDerivative (fun i => (h i : ℚ)))
        (congrArg NilpotentLieBCHGroup.coord hqg)
    rwa [heq] at hout
  · intro g r hg hr
    let q := F.realAdaptedPolynomialGroupLift (fun _ : σ => 1) b ω hF g
    let t := F.realAdaptedPolynomialGroupLift (fun _ : σ => 1) b ω hF r
    have hqg := F.realAdaptedPolynomialGroupHom_lift (fun _ : σ => 1) b ω hF g
    have htr := F.realAdaptedPolynomialGroupHom_lift (fun _ : σ => 1) b ω hF r
    have hq := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) l q).mpr
      (by simpa only [q, hqg] using hg)
    have ht := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) l t).mpr
      (by simpa only [t, htr] using hr)
    have hout := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) m
      (⟨dualAdjoint q t.coord⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp (had q t.coord hq ht)
    have heq : F.realAdaptedPolynomialGroupHom (fun _ => 1)
        (⟨dualAdjoint q t.coord⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1)) = ⟨dualAdjoint g r.coord⟩ := by
      apply NilpotentLieBCHGroup.ext
      change F.realAdaptedPolynomialTensor (fun _ => 1) (dualAdjoint q t.coord) = _
      rw [F.realAdaptedAdjoint_tensor]
      change dualAdjoint (F.realAdaptedPolynomialGroupHom (fun _ => 1) q)
        (F.realAdaptedPolynomialGroupHom (fun _ => 1) t).coord = _
      rw [hqg, htr]
    rwa [heq] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          ∀ i : σ, CoefficientGrid (b.baseChange ℝ) m (formalLogDerivative i A)) ∧
        (∀ (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
          (Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          CoefficientGrid (b.baseChange ℝ) l Q →
          CoefficientGrid (b.baseChange ℝ) m (dualAdjoint A Q)) := by
  obtain ⟨C, hC, hgrid⟩ := exists_real_adapted_dual_grid s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  classical
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro A hA hAgrid i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp
      (hlog x hxgrid (Pi.single i 1))
    have hsingle : (fun j => ((Pi.single i 1 : σ → ℤ) j : ℚ)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [hsingle, F.realAdaptedLogDerivative_eq_formal, hx] at hout
    exact hout
  · intro A Q hA hQ hAgrid hQgrid
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hygrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l y := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l y).mpr
      rwa [hy]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp (had G y hxgrid hygrid)
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hout
    exact hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem polynomialRationalGrid_add_sub {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (w : σ → ℕ) (l : ℕ)
    (a b c : (F.realification.adaptedPolynomialFiltration w).Group)
    (ha : F.PolynomialRationalGrid e w l a) (hb : F.PolynomialRationalGrid e w l b)
    (hc : F.PolynomialRationalGrid e w l c) :
    F.PolynomialRationalGrid e w l ⟨a.coord + b.coord - c.coord⟩ := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  obtain ⟨zc, hzc⟩ := hc
  refine ⟨fun z => za z + zb z - zc z, ?_⟩
  funext z
  have hA := congrFun hza z
  have hB := congrFun hzb z
  have hC := congrFun hzc z
  change (za z : ℝ) = (l : ℝ) * (e.baseChange ℝ).repr
    (coefficients (a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2 at hA
  change (zb z : ℝ) = (l : ℝ) * (e.baseChange ℝ).repr
    (coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2 at hB
  change (zc z : ℝ) = (l : ℝ) * (e.baseChange ℝ).repr
    (coefficients (c.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2 at hC
  change ((za z + zb z - zc z : ℤ) : ℝ) = (l : ℝ) * (e.baseChange ℝ).repr
    (coefficients ((a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) +
      (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) -
      (c.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) z.1) z.2
  simp only [Int.cast_add, Int.cast_sub, map_sub, map_add, Finsupp.add_apply, Finsupp.sub_apply]
  rw [hA, hB, hC]
  ring

theorem exists_rational_derivative_correction_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ v D k : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
          F.PolynomialRationalGrid b (fun _ => 1) l v →
          F.PolynomialRationalGrid b (fun _ => 1) l D →
          F.PolynomialRationalGrid b (fun _ => 1) l k →
          ∀ h : σ → ℤ, F.PolynomialRationalGrid b (fun _ => 1) m
            ⟨v.coord + dualAdjoint D k.coord -
              F.realification.adaptedLogDerivative (fun i => (h i : ℚ)) D.coord⟩ := by
  have hgridExists := exists_polynomial_dual_grid s
  obtain ⟨C, hC, hgrid⟩ := hgridExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  have hdata := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro v D k hv hD hk h
  exact F.polynomialRationalGrid_add_sub b (fun _ => 1) m v
    ⟨dualAdjoint D k.coord⟩ ⟨F.realification.adaptedLogDerivative (fun i => (h i : ℚ)) D.coord⟩
    (F.polynomialRationalGrid_of_dvd b (fun _ => 1) hl hlm v hv) (had D k hD hk) (hlog D hD h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

theorem exists_polynomial_log_derivative_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g →
      ∀ h : σ → ℚ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + C) ^ C))
        ⟨F.realification.adaptedLogDerivative h g.coord⟩ := by
  have hboundExists := exists_real_adapted_log_derivative_bound s a
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT g hg h hh
  let q := F.realAdaptedPolynomialGroupLift (fun _ : σ => 1) b ω hF g
  have hqg := F.realAdaptedPolynomialGroupHom_lift (fun _ : σ => 1) b ω hF g
  have hq := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1)
    T hT (Real.exp_nonneg _) q).mpr (by simpa only [q, hqg] using hg)
  have hout := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1)
    T hT (Real.exp_nonneg _)
    (⟨F.realAdaptedLogDerivative h q.coord⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp
    (hbound F b ω hF H p hH hp hι hσ hHp hc T hT q.coord hq h hh)
  have heq : F.realAdaptedPolynomialGroupHom (fun _ => 1)
      (⟨F.realAdaptedLogDerivative h q.coord⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1)) =
      ⟨F.realification.adaptedLogDerivative h g.coord⟩ := by
    apply NilpotentLieBCHGroup.ext
    change F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedLogDerivative h q.coord) = _
    rw [F.realAdaptedLogDerivative_tensor]
    exact congrArg (F.realification.adaptedLogDerivative h) (congrArg NilpotentLieBCHGroup.coord hqg)
  rwa [heq] at hout

theorem exists_polynomial_adjoint_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g →
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) r →
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + C) ^ C)) ⟨dualAdjoint g r.coord⟩ := by
  have hboundExists := exists_scaled_polynomial_dual_bound s a
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT g r hg hr
  let q := F.realAdaptedPolynomialGroupLift (fun _ : σ => 1) b ω hF g
  let t := F.realAdaptedPolynomialGroupLift (fun _ : σ => 1) b ω hF r
  have hqg := F.realAdaptedPolynomialGroupHom_lift (fun _ : σ => 1) b ω hF g
  have htr := F.realAdaptedPolynomialGroupHom_lift (fun _ : σ => 1) b ω hF r
  have hq := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1)
    T hT (Real.exp_nonneg _) q).mpr (by simpa only [q, hqg] using hg)
  have ht := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1)
    T hT (Real.exp_nonneg _) t).mpr (by simpa only [t, htr] using hr)
  have hh := (hbound F b ω hF (fun _ : σ => 1) (by simp) H p hH hp hι hσ hHp hc T hT).2
    q t.coord hq ht
  have hout := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1)
    T hT (Real.exp_nonneg _)
    (⟨dualAdjoint q t.coord⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hh
  have heq : F.realAdaptedPolynomialGroupHom (fun _ => 1)
      (⟨dualAdjoint q t.coord⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1)) = ⟨dualAdjoint g r.coord⟩ := by
    apply NilpotentLieBCHGroup.ext
    change F.realAdaptedPolynomialTensor (fun _ => 1) (dualAdjoint q t.coord) = _
    rw [F.realAdaptedAdjoint_tensor]
    change dualAdjoint (F.realAdaptedPolynomialGroupHom (fun _ => 1) q)
      (F.realAdaptedPolynomialGroupHom (fun _ => 1) t).coord = _
    rw [hqg, htr]
  rwa [heq] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem polynomialSlowBound_add_sub {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (w : σ → ℕ) (T : σ → ℝ)
    (M₁ M₂ M₃ : ℝ) (a b c : (F.realification.adaptedPolynomialFiltration w).Group)
    (ha : F.PolynomialSlowBound e w T M₁ a) (hb : F.PolynomialSlowBound e w T M₂ b)
    (hc : F.PolynomialSlowBound e w T M₃ c) :
    F.PolynomialSlowBound e w T (M₁ + M₂ + M₃) ⟨a.coord + b.coord - c.coord⟩ := by
  intro α i
  change |(e.baseChange ℝ).repr (coefficients
    ((a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) +
      (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) -
      (c.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α) i| ≤ _
  simp only [map_sub, map_add, Finsupp.add_apply, Finsupp.sub_apply]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) (le_refl _)).trans
  apply (add_le_add (add_le_add (ha α i) (hb α i)) (hc α i)).trans
  exact le_of_eq (by ring)

theorem exists_slow_derivative_correction_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ A e u : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) A →
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) e →
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) u →
      ∀ h : σ → ℚ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + C) ^ C))
        ⟨dualAdjoint A⁻¹ (e.coord + u.coord - F.realification.adaptedLogDerivative h A.coord)⟩ := by
  have hlogExists := exists_polynomial_log_derivative_bound s a
  obtain ⟨cl, _, hlog⟩ := hlogExists
  have hadExists := exists_polynomial_adjoint_bound s 1
  obtain ⟨ca, _, had⟩ := hadExists
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a +
    (Polynomial.X + Polynomial.C cl) ^ cl + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C ca) ^ ca
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT A e u hA he hu h hh
  let q := (p + 2) ^ a + (p + cl) ^ cl + p + 2
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hl0 : 0 ≤ (p + cl) ^ cl := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hfinal : (q + ca) ^ ca ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hsum : Real.exp ((p + 2) ^ a) + Real.exp ((p + 2) ^ a) + Real.exp ((p + cl) ^ cl) ≤
      Real.exp (q + 2) := by
    have he₁ : Real.exp ((p + 2) ^ a) ≤ Real.exp ((p + 2) ^ a + (p + cl) ^ cl) :=
      Real.exp_le_exp.mpr (le_add_of_nonneg_right hl0)
    have he₂ : Real.exp ((p + cl) ^ cl) ≤ Real.exp ((p + 2) ^ a + (p + cl) ^ cl) :=
      Real.exp_le_exp.mpr (le_add_of_nonneg_left ha0)
    calc
      _ ≤ 3 * Real.exp ((p + 2) ^ a + (p + cl) ^ cl) := by linarith
      _ ≤ Real.exp 2 * Real.exp ((p + 2) ^ a + (p + cl) ^ cl) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 2]) (Real.exp_nonneg _)
      _ = Real.exp (2 + ((p + 2) ^ a + (p + cl) ^ cl)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  let k : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨e.coord + u.coord - F.realification.adaptedLogDerivative h A.coord⟩
  have hk := F.polynomialSlowBound_add_sub b (fun _ => 1) T _ _ _ e u
    ⟨F.realification.adaptedLogDerivative h A.coord⟩ he hu
    (hlog F b ω hF H p hH hp hι hσ hHp hc T hT A hA h hh)
  have hk' : F.PolynomialSlowBound b (fun _ => 1) T (Real.exp (q + 2)) k :=
    F.polynomialSlowBound_mono b (fun _ => 1) T hT hsum k hk
  have hAi : F.PolynomialSlowBound b (fun _ => 1) T (Real.exp (q + 2)) A⁻¹ :=
    F.polynomialSlowBound_mono b (fun _ => 1) T hT (Real.exp_le_exp.mpr haq) A⁻¹
      ((F.polynomialSlowBound_inv_iff b (fun _ => 1) T _ A).mpr hA)
  have hout := had F b ω hF H q hH hq (hι.trans hpq) (hσ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hc T hT A⁻¹ k
    (by simpa only [pow_one] using hAi) (by simpa only [pow_one] using hk')
  exact F.polynomialSlowBound_mono b (fun _ => 1) T hT (Real.exp_le_exp.mpr hfinal) _ hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialSlowBound_sub (b : Basis ι ℚ L) (w : σ → ℕ) (T : σ → ℝ)
    (M N : ℝ) (a c : (F.realification.adaptedPolynomialFiltration w).Group)
    (ha : F.PolynomialSlowBound b w T M a) (hc : F.PolynomialSlowBound b w T N c) :
    F.PolynomialSlowBound b w T (M + N) ⟨a.coord - c.coord⟩ := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients
    ((a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) -
      (c.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α) i| ≤ _
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (ha α i) (hc α i)).trans_eq (add_div M N _).symm)

theorem polynomialRationalGrid_sub (b : Basis ι ℚ L) (w : σ → ℕ) (l : ℕ)
    (a c : (F.realification.adaptedPolynomialFiltration w).Group)
    (ha : F.PolynomialRationalGrid b w l a) (hc : F.PolynomialRationalGrid b w l c) :
    F.PolynomialRationalGrid b w l ⟨a.coord - c.coord⟩ := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zc, hzc⟩ := hc
  refine ⟨za - zc, ?_⟩
  funext z
  have hA := congrFun hza z
  have hC := congrFun hzc z
  change (za z : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients (a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2 at hA
  change (zc z : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients (c.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2 at hC
  change ((za z - zc z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients ((a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) -
      (c.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) z.1) z.2
  simp only [Int.cast_sub, map_sub, Finsupp.sub_apply, mul_sub, hA, hC]

theorem polynomial_common_derivative_difference [Fintype σ]
    (b : Basis ι ℚ L) (T : σ → ℝ) (M N : ℝ) (l : ℕ)
    (V : Submodule ℚ (F.realification.adaptedLieSubalgebra (fun _ : σ => 1)))
    (B S S₀ R R₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h h₀ : σ → ℚ) (ZB : F.realification.adaptedLieSubalgebra (fun _ : σ => 1))
    (hh : F.realification.adaptedLogDerivative h B.coord -
      (S.coord + dualAdjoint B R.coord + ZB) ∈ V)
    (hh₀ : F.realification.adaptedLogDerivative h₀ B.coord -
      (S₀.coord + dualAdjoint B R₀.coord + ZB) ∈ V)
    (hS : F.PolynomialSlowBound b (fun _ => 1) T M S)
    (hS₀ : F.PolynomialSlowBound b (fun _ => 1) T N S₀)
    (hR : F.PolynomialRationalGrid b (fun _ => 1) l R)
    (hR₀ : F.PolynomialRationalGrid b (fun _ => 1) l R₀) :
    (F.realification.adaptedLogDerivative (h - h₀) B.coord -
      ((S.coord - S₀.coord) + dualAdjoint B (R.coord - R₀.coord)) ∈ V) ∧
      F.PolynomialSlowBound b (fun _ => 1) T (M + N) ⟨S.coord - S₀.coord⟩ ∧
      F.PolynomialRationalGrid b (fun _ => 1) l ⟨R.coord - R₀.coord⟩ :=
  ⟨F.realification.adapted_common_derivative_difference V B h h₀
      S.coord S₀.coord R.coord R₀.coord ZB hh hh₀,
    F.polynomialSlowBound_sub b (fun _ => 1) T M N S S₀ hS hS₀,
    F.polynomialRationalGrid_sub b (fun _ => 1) l R R₀ hR hR₀⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
