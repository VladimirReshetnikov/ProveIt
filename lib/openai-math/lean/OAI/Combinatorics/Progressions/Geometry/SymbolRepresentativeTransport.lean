import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ M : Type*} [Fintype ι] [Fintype κ] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration M s) (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : Basis κ ℚ M)

omit [Fintype κ] in
theorem realSymbolRepresentative_slow_original_coordinates (w : σ → ℕ)
    (T : σ → ℝ) (hT : ∀ j, 0 < T j) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (E : F.RealPolynomialSymbolGroup w) (hE : F.SymbolSlowBound b ω hF w T (Real.exp p) E)
    (α : σ →₀ ℕ) (i : κ) :
    |(e.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hF w E.coord) α) i| ≤
      Real.exp ((p + 3) ^ 2) / monomialScale T α := by
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
  calc
    _ ≤ (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * (Real.exp p / monomialScale T α) :=
      real_basis_coordinates_bound b e (fun i j => rationalHeightLE_ceil_exp (hentries j i)) _
        (fun j => F.realSymbolRepresentative_slow_coefficients b ω hF w T hT
          (Real.exp_pos p).le E hE α j) i
    _ = ((Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p) / monomialScale T α := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (monomialScale_pos T hT α).le

theorem realSymbolRepresentative_original_grid (w : σ → ℕ) (l : ℕ)
    (R : F.RealPolynomialSymbolGroup w) (hR : F.SymbolRationalGrid b ω hF w l R)
    (α : σ →₀ ℕ) :
    (fun i => (e.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hF w R.coord) α) i)
      ∈ realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
  obtain ⟨z, hz⟩ := F.realSymbolRepresentative_rational_coefficients b ω hF w l R hR
  apply real_basis_coordinates_grid b e l
  exact ⟨fun j => z (α, j), funext (fun j => congrFun hz (α, j))⟩

theorem original_coordinate_denominator_bound {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (l : ℕ) (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator (fun i j => e.repr (b j) i) * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 3 + p) := by
  have hD : (matrixDenominator (fun i j => e.repr (b j) i) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power (fun i j => e.repr (b j) i) hp 1 hκ hι
    intro i j
    exact ((rationalLogHeight_le_iff _ _).mp (hentries j i)).2.trans
      (Real.exp_le_exp.mpr (by simp))
  rw [Nat.cast_mul]
  exact (mul_le_mul hD hl (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
