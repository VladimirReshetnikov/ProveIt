import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (e : Basis κ ℚ L)
  (w : σ → ℕ)

theorem polynomialRationalGrid_change_basis (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.PolynomialRationalGrid e w
      (matrixDenominator (fun i j => e.repr (b j) i) * l) g := by
  classical
  obtain ⟨z, hz⟩ := hg
  have hgrid (α : σ →₀ ℕ) :
      (fun i => (e.baseChange ℝ).repr
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i) ∈
        realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
    apply real_basis_coordinates_grid b e l
    exact ⟨fun j => z (α, j), funext fun j => congrFun hz (α, j)⟩
  choose a ha using hgrid
  exact ⟨fun z => a z.1 z.2, funext fun z => congrFun (ha z.1) z.2⟩

omit [Fintype κ] in
theorem polynomialSlowBound_change_basis_exp (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T (Real.exp p) g) :
    F.PolynomialSlowBound e w T (Real.exp ((p + 3) ^ 2)) g := by
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hdim' : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hbound : (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p ≤ Real.exp ((p + 3) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  intro α i
  calc
    _ ≤ (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * (Real.exp p / monomialScale T α) :=
      real_basis_coordinates_bound b e (fun i j => rationalHeightLE_ceil_exp (hentries j i)) _
        (fun j => hg α j) i
    _ = ((Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p) / monomialScale T α := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

end OAI
