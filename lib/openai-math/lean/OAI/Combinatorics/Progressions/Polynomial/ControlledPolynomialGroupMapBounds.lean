import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialRationalGrid_iff_coefficients [Finite ι] (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔ ∀ α,
      (b.baseChange ℝ).equivFun
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) ∈
          realDenominatorGrid l := by
  classical
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext fun i => congrFun ha (α, i)⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext fun z => congrFun (ha z.1) z.2⟩

theorem polynomialRationalGrid_inv (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.PolynomialRationalGrid b w l g⁻¹ := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => -a z, funext fun z => ?_⟩
  change ((-a z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients ((g⁻¹).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [coord_inv]
  change ((-a z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients (-(g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) z.1) z.2
  simp only [map_neg, Finsupp.neg_apply, Int.cast_neg, mul_neg]
  exact congrArg Neg.neg (congrFun ha z)

theorem filteredRealPolynomialSection_rationalGrid [Fintype ι] [Fintype κ]
    [DecidableEq κ] (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (l : ℕ)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialRationalGrid c w l g) :
    F.PolynomialRationalGrid b w
      (matrixDenominator (LinearMap.toMatrix c b S) * l)
      (F.filteredRealPolynomialSection G w S hS g) := by
  rw [F.polynomialRationalGrid_iff_coefficients]
  intro α
  have hc := (G.polynomialRationalGrid_iff_coefficients c w l g).mp hg α
  have ho := realified_linear_coordinate_grid c b S l _ hc
  change (b.baseChange ℝ).equivFun (coefficients
    (map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) α) ∈ _
  simpa only [coefficients_map, LinearMap.restrictScalars_apply] using ho

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (b : Basis ι ℚ L) (c : Basis κ ℚ M)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)

theorem realPolynomialGroupMap_slow_exp
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T A g) :
    G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ 3) * A)
      (F.realPolynomialGroupMap G φ hφ w g) := by
  classical
  let Q := LinearMap.toMatrix b c φ.toLinearMap
  have hQ : ∀ i j, RationalHeightLE (Q i j) H := by
    simpa only [Q, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using hentries
  have hnum : ∀ i j, ((Q i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 1) := by
    intro i j
    exact (Nat.cast_le.mpr (hQ i j).1).trans
      (hHp.trans (Real.exp_le_exp.mpr (by simp)))
  intro α i
  change |(c.baseChange ℝ).repr (coefficients
    ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α) i| ≤ _
  rw [F.realPolynomialGroupMap_log G φ hφ w, coefficients_map]
  change |(c.baseChange ℝ).equivFun (φ.toLinearMap.baseChange ℝ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) i| ≤ _
  exact rational_coordinate_map_weighted_exp (b.baseChange ℝ) (c.baseChange ℝ)
    (φ.toLinearMap.baseChange ℝ) Q (realified_linear_coordinate_matrix b c φ.toLinearMap)
    (fun _ : ι => ()) (fun _ : κ => ()) (fun _ _ h => (h rfl).elim)
    hp hsource 1 (by decide) hnum (fun _ : Unit => monomialScale T α)
    (fun _ => monomialScale_pos T hT α) hA
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) (hg α) i

theorem exists_realPolynomialGroupMap_grid
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (htarget : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialRationalGrid b w l g →
        G.PolynomialRationalGrid c w m (F.realPolynomialGroupMap G φ hφ w g) := by
  classical
  let Q := LinearMap.toMatrix b c φ.toLinearMap
  have hQ : ∀ i j, RationalHeightLE (Q i j) H := by
    simpa only [Q, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using hentries
  refine ⟨l * matrixDenominator Q, Nat.mul_pos hl (matrixDenominator_pos Q),
    matrixDenominator_allowance_le_exp Q l H hQ hp htarget hsource hHp hlp,
    dvd_mul_right l (matrixDenominator Q), ?_⟩
  intro g hg
  rw [G.polynomialRationalGrid_iff_coefficients]
  intro α
  have hc := (F.polynomialRationalGrid_iff_coefficients b w l g).mp hg α
  have ho := realified_linear_coordinate_grid b c φ.toLinearMap l _ hc
  rw [F.realPolynomialGroupMap_log G φ hφ w, coefficients_map]
  change (c.baseChange ℝ).equivFun (φ.toLinearMap.baseChange ℝ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) ∈
      realDenominatorGrid (l * matrixDenominator Q)
  simpa only [Q, Nat.mul_comm] using ho

end Erdos3.NilpotentLieFiltration

end

end OAI
