/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.CoordinateProjectionBounds
import OAI.Combinatorics.Progressions.Linear.RescaledLieBasis
import OAI.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
import OAI.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ a b' : F.PolynomialSymbolGroup w,
          (fun z => (F.polynomialSymbolBasis b ω hlayers w).repr a.coord z) ∈ denominatorGrid l →
          (fun z => (F.polynomialSymbolBasis b ω hlayers w).repr b'.coord z) ∈ denominatorGrid l →
          (fun z => (F.polynomialSymbolBasis b ω hlayers w).repr (a * b').coord z) ∈ denominatorGrid m) ∧
        (∀ a : F.PolynomialSymbolGroup w,
          (fun z => (F.polynomialSymbolBasis b ω hlayers w).repr a.coord z) ∈ denominatorGrid l →
          (fun z => (F.polynomialSymbolBasis b ω hlayers w).repr (a⁻¹).coord z) ∈ denominatorGrid m) := by
  obtain ⟨K, _, hK⟩ := exists_bch_rational_closure s
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j k, RationalHeightLE (lieStructureConstants B i j k) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  obtain ⟨m, hm, hmp, hlm, hmul⟩ := hK B H q hq hdim
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hstruct l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, ?_, ?_⟩
  · intro a b' ha hb'
    exact hmul a.coord b'.coord ha hb'
  · intro a ha
    have hneg := denominatorGrid_subset_of_dvd hlm (denominatorGrid_neg l ha)
    change B.equivFun (-a.coord) ∈ denominatorGrid m
    rw [map_neg]
    exact hneg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

abbrev RealPolynomialSymbol {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  ℝ ⊗[ℚ] F.PolynomialSymbol w

abbrev RealPolynomialSymbolGroup {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  NilpotentLieBCHGroup (F.RealPolynomialSymbol w) s
    (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))

theorem exists_real_symbol_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ a b' : F.RealPolynomialSymbolGroup w,
          (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr a.coord z)
            ∈ realDenominatorGrid l →
          (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr b'.coord z)
            ∈ realDenominatorGrid l →
          (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (a * b').coord z)
            ∈ realDenominatorGrid m) ∧
        (∀ a : F.RealPolynomialSymbolGroup w,
          (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr a.coord z)
            ∈ realDenominatorGrid l →
          (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (a⁻¹).coord z)
            ∈ realDenominatorGrid m) := by
  obtain ⟨C, hC, hbound⟩ := exists_symbol_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  obtain ⟨m, hm, hmp, hlm, hmul, hinv⟩ :=
    hbound F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · exact NilpotentLieBCHGroup.realification_grid_mul
      (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.polynomialSymbolBasis b ω hlayers w) l m hl hmul
  · exact NilpotentLieBCHGroup.realification_grid_inv
      (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.polynomialSymbolBasis b ω hlayers w) l m hl hinv

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolBasis_bracket_support (u v z : SymbolBasisIndex w ω)
    (h : ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      ⁅(F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ u,
        (F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ v⁆ z ≠ 0) :
    u.val.1 + v.val.1 = z.val.1 := by
  classical
  by_contra hn
  apply h
  rw [realLieBasis_structure]
  change (((F.polynomialSymbolBasis b ω hlayers w).repr
    ⁅F.polynomialSymbolBasis b ω hlayers w u,
      F.polynomialSymbolBasis b ω hlayers w v⁆ z : ℚ) : ℝ) = 0
  simp only [F.polynomialSymbolBasis_bracket, hn, ↓reduceIte, Rat.cast_zero]

noncomputable def scaledRealPolynomialSymbolBasis (T : σ → ℝ) (hT : ∀ i, 0 < T i) :
    Basis (SymbolBasisIndex w ω) ℝ (F.RealPolynomialSymbol w) :=
  inverseScaledBasis ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
    (fun z => monomialScale T z.val.1) (fun z => monomialScale_pos T hT z.val.1)

theorem scaledRealPolynomialSymbolBasis_repr (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr x z =
      monomialScale T z.val.1 *
        ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z :=
  inverseScaledBasis_repr _ _ _ _ _

theorem scaledRealPolynomialSymbolBasis_structure (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (u v z : SymbolBasisIndex w ω) :
    (F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr
      ⁅F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT u,
        F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT v⁆ z =
      (lieStructureConstants (F.polynomialSymbolBasis b ω hlayers w) u v z : ℝ) := by
  apply Eq.trans (inverseScaledBasis_bracket _ _ _ ?_ u v z)
  · exact realLieBasis_structure _ u v z
  · intro i j k h
    have hijk := F.realPolynomialSymbolBasis_bracket_support b ω hlayers w i j k h
    rw [← hijk, monomialScale_add]

theorem scaledRealPolynomialSymbolBasis_bound_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) (M : ℝ) :
    |(F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr x z| ≤ M ↔
      |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z| ≤
        M / monomialScale T z.val.1 := by
  rw [F.scaledRealPolynomialSymbolBasis_repr, abs_mul,
    abs_of_pos (monomialScale_pos T hT z.val.1), le_div_iff₀ (monomialScale_pos T hT z.val.1)]
  rw [mul_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem realDenominatorGrid_neg {ι : Type*} (l : ℕ) {x : ι → ℝ}
    (hx : x ∈ realDenominatorGrid l) : -x ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * x i at hi
  change ((-z i : ℤ) : ℝ) = (l : ℝ) * (-x i)
  rw [Int.cast_neg, hi, mul_neg]

namespace NilpotentLieFiltration

open Module

def SymbolRationalGrid {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (l : ℕ) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z)
    ∈ realDenominatorGrid l

theorem symbolRationalGrid_inv {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (l : ℕ) {g : F.RealPolynomialSymbolGroup w}
    (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    F.SymbolRationalGrid b ω hlayers w l g⁻¹ := by
  change (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (-g.coord) z)
    ∈ realDenominatorGrid l
  have heq : (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (-g.coord) z) =
      -(fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z) := by
    funext z
    simp only [map_neg, Finsupp.neg_apply, Pi.neg_apply]
  rw [heq]
  exact realDenominatorGrid_neg l hg

theorem exists_symbol_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (F.RealPolynomialSymbolGroup w), rs.length ≤ k →
          (∀ r ∈ rs, F.SymbolRationalGrid b ω hlayers w l r) →
          F.SymbolRationalGrid b ω hlayers w m rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_real_bch_rational_product_bound s k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hK B H q
    (F.polynomialSymbol_lowerCentralSeries_eq_bot w) hq hdim
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hstruct l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, hprod⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def SymbolSlowBound {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  ∀ z : SymbolBasisIndex w ω,
    |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤
      M / monomialScale T z.val.1

@[simp] theorem symbolSlowBound_inv_iff {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound b ω hlayers w T M g⁻¹ ↔ F.SymbolSlowBound b ω hlayers w T M g := by
  simp only [SymbolSlowBound, NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply, abs_neg]

theorem exists_symbol_slow_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ rs : List (F.RealPolynomialSymbolGroup w), rs.length ≤ k →
      (∀ r ∈ rs, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) r) →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_bch_fixed_product_exp_bound s a k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT rs hlen hrs
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let E := F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, algebraMap ℚ ℝ (lieStructureConstants B i j z) = E.repr ⁅E i, E j⁆ z :=
    fun i j z => (F.scaledRealPolynomialSymbolBasis_structure b ω hlayers w T hT i j z).symm
  have hheight : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  have hinput : ∀ r ∈ rs, ∀ z, |E.repr r.coord z| ≤ Real.exp ((q + 2) ^ a) := by
    intro r hr z
    have hscaled := (F.scaledRealPolynomialSymbolBasis_bound_iff b ω hlayers w T hT
      r.coord z (Real.exp ((p + 2) ^ a))).mpr (hrs r hr z)
    exact hscaled.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  intro z
  apply (F.scaledRealPolynomialSymbolBasis_bound_iff b ω hlayers w T hT
    rs.prod.coord z (Real.exp ((p + C) ^ C))).mp
  exact (hK E (lieStructureConstants B) H q
    (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))
    rs hstruct hq hdim hlen (hHp.trans (Real.exp_le_exp.mpr hpq)) hheight hinput z).trans
      (Real.exp_le_exp.mpr hpoly)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

include hlayers

theorem symbolBasisIndex_monomial_ne_zero (z : SymbolBasisIndex w ω) : z.val.1 ≠ 0 := by
  intro hz
  have hd := z.property
  rw [hz, map_zero] at hd
  have hp := F.adaptedBasis_weight_pos b ω hlayers z.val.2
  omega

theorem symbolSlowBound_log_norm [Fintype (SymbolBasisIndex w ω)]
    (T : σ → ℝ) {R M : ℝ} (hR : 1 ≤ R) (hT : ∀ i, R ≤ T i) (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g) :
    ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun g.coord‖ ≤ M / R := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hM (zero_le_one.trans hR))).mpr
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤ M / R
  have hscale := le_monomialScale_of_ne_zero T hR hT
    (F.symbolBasisIndex_monomial_ne_zero b ω hlayers w z)
  exact (hg z).trans (div_le_div_of_nonneg_left hM (zero_lt_one.trans_le hR) hscale)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem sub_realGradeTruncation_mem (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    x - basisBelowProjection (b.baseChange ℝ) w j x ∈ F.realification.layer j := by
  change x - basisBelowProjection (b.baseChange ℝ) w j x ∈ (F.realLayer j).toSubmodule
  rw [F.realLayer_eq_span_basis b j {i | j ≤ w i} (hlayers j)]
  exact sub_basisBelowProjection_mem (b.baseChange ℝ) w j x

include hlayers in
theorem realGradeTruncation_eq_iff (j : ℕ) (x y : ℝ ⊗[ℚ] L) :
    basisBelowProjection (b.baseChange ℝ) w j x = basisBelowProjection (b.baseChange ℝ) w j y ↔
      x - y ∈ F.realification.layer j := by
  change _ ↔ x - y ∈ (F.realLayer j).toSubmodule
  rw [F.realLayer_eq_span_basis b j {i | j ≤ w i} (hlayers j)]
  exact basisBelowProjection_eq_iff (b.baseChange ℝ) w j x y

include hlayers in
theorem realGradeTruncation_quotient (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    lieQuotientMap (F.realification.layerIdeal j) (basisBelowProjection (b.baseChange ℝ) w j x) =
      lieQuotientMap (F.realification.layerIdeal j) x := by
  have h := (lieQuotientMap_eq_zero (F.realification.layerIdeal j) _).mpr
    (F.sub_realGradeTruncation_mem b w hlayers j x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

noncomputable def truncateRealGrades (j : ℕ) (g : F.realification.Group) : F.realification.Group :=
  ⟨basisBelowProjection (b.baseChange ℝ) w j g.coord⟩

@[simp] theorem truncateRealGrades_coord (j : ℕ) (g : F.realification.Group) :
    (F.truncateRealGrades b w j g).coord = basisBelowProjection (b.baseChange ℝ) w j g.coord := rfl

include hlayers in
theorem truncateRealGrades_quotient (j : ℕ) (g : F.realification.Group) :
    NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (F.truncateRealGrades b w j g) =
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradeTruncation_quotient b w hlayers j g.coord

include hlayers in

theorem truncateRealGrades_mem_of_quotient_mem (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (j : ℕ) (g : F.realification.Group)
    (hg : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) g ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))) :
    (F.truncateRealGrades b w j g).coord ∈ U := by
  obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hg
  have hdiff : g.coord - u.coord ∈ F.realification.layer j := by
    apply (lieQuotientMap_eq_zero (F.realification.layerIdeal j) _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg NilpotentLieBCHGroup.coord heq).symm
  have ht := (F.realGradeTruncation_eq_iff b w hlayers j g.coord u.coord).mpr hdiff
  change basisBelowProjection (b.baseChange ℝ) w j g.coord ∈ U
  rw [ht]
  exact hU.below_mem (b.baseChange ℝ) w U.toSubmodule j u.coord hu

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem symbolSlowBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M N : ℝ} (hMN : M ≤ N)
    (g : F.RealPolynomialSymbolGroup v) (hg : F.SymbolSlowBound b w hlayers v T M g) :
    F.SymbolSlowBound b w hlayers v T N g := by
  intro z
  exact (hg z).trans (div_le_div_of_nonneg_right hMN (le_of_lt (monomialScale_pos T hT z.val.1)))

theorem symbolRationalGrid_mono {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (g : F.RealPolynomialSymbolGroup v) (hg : F.SymbolRationalGrid b w hlayers v l g) :
    F.SymbolRationalGrid b w hlayers v m g :=
  realDenominatorGrid_subset_of_dvd hl hlm hg

noncomputable def truncateRealSymbol (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    F.RealPolynomialSymbolGroup v :=
  (F.polynomialSymbolFiltration v).truncateRealGrades
    (F.polynomialSymbolBasis b w hlayers v) (fun z => w z.val.2) j g

@[simp] theorem truncateRealSymbol_coord (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    (F.truncateRealSymbol b w hlayers v j g).coord =
      basisBelowProjection ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ)
        (fun z => w z.val.2) j g.coord := rfl

theorem truncateRealSymbol_slow (j : ℕ) (g : F.RealPolynomialSymbolGroup v)
    (T : σ → ℝ) (M : ℝ) (hg : F.SymbolSlowBound b w hlayers v T M g) :
    F.SymbolSlowBound b w hlayers v T M (F.truncateRealSymbol b w hlayers v j g) := by
  intro z
  exact (basisCoordinateProjection_abs_repr_le
    ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ) {z | w z.val.2 < j} g.coord z).trans (hg z)

theorem truncateRealSymbol_rational (j : ℕ) (g : F.RealPolynomialSymbolGroup v)
    (l : ℕ) (hg : F.SymbolRationalGrid b w hlayers v l g) :
    F.SymbolRationalGrid b w hlayers v l (F.truncateRealSymbol b w hlayers v j g) :=
  basisCoordinateProjection_real_grid ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ)
    {z | w z.val.2 < j} l g.coord hg

theorem truncateRealSymbol_quotient (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    NilpotentLieBCHGroup.quotientHom
        ((F.polynomialSymbolFiltration v).realification.layerIdeal j)
        (F.truncateRealSymbol b w hlayers v j g) =
      NilpotentLieBCHGroup.quotientHom ((F.polynomialSymbolFiltration v).realification.layerIdeal j) g :=
  (F.polynomialSymbolFiltration v).truncateRealGrades_quotient
    (F.polynomialSymbolBasis b w hlayers v) (fun z => w z.val.2)
    (F.polynomialSymbolFiltration_layer b w hlayers v) j g

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ : Type*}

def reindexSymbolBasisIndex (w : σ → ℕ) (ω : ι → ℕ) (e : ι ≃ κ) :
    SymbolBasisIndex w ω ≃ SymbolBasisIndex w (fun k => ω (e.symm k)) where
  toFun z := ⟨(z.val.1, e z.val.2), by simpa only [Equiv.symm_apply_apply] using z.property⟩
  invFun z := ⟨(z.val.1, e.symm z.val.2), z.property⟩
  left_inv z := by apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  right_inv z := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))
  (w : σ → ℕ)

theorem polynomialSymbolBasis_repr_reindex (x : F.PolynomialSymbol w)
    (z : SymbolBasisIndex w (fun k => ω (e.symm k))) :
    (F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).repr x z =
      (F.polynomialSymbolBasis b ω hF w).repr x ((reindexSymbolBasisIndex w ω e).symm z) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolBasis_repr_map, F.polynomialSymbolBasis_repr_map,
    Basis.repr_reindex_apply]
  rfl

theorem realPolynomialSymbolBasis_repr_reindex (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w (fun k => ω (e.symm k))) :
    ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr x z =
      ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr x
        ((reindexSymbolBasisIndex w ω e).symm z) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.polynomialSymbolBasis_repr_reindex b ω hF e hF' w]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem symbolSlowBound_reindex_iff (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound (b.reindex e) (fun k => ω (e.symm k)) hF' w T M g ↔
      F.SymbolSlowBound b ω hF w T M g := by
  constructor
  · intro hg z
    have hz := hg (reindexSymbolBasisIndex w ω e z)
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w,
      Equiv.symm_apply_apply] at hz
    exact hz
  · intro hg z
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w]
    exact hg ((reindexSymbolBasisIndex w ω e).symm z)

theorem symbolRationalGrid_reindex_iff (l : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolRationalGrid (b.reindex e) (fun k => ω (e.symm k)) hF' w l g ↔
      F.SymbolRationalGrid b ω hF w l g := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a (reindexSymbolBasisIndex w ω e z), ?_⟩
    funext z
    have hz := congrFun ha (reindexSymbolBasisIndex w ω e z)
    change (a (reindexSymbolBasisIndex w ω e z) : ℝ) = (l : ℝ) *
      ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr
        g.coord (reindexSymbolBasisIndex w ω e z) at hz
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w,
      Equiv.symm_apply_apply] at hz
    exact hz
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a ((reindexSymbolBasisIndex w ω e).symm z), ?_⟩
    funext z
    change (a ((reindexSymbolBasisIndex w ω e).symm z) : ℝ) = (l : ℝ) *
      ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr
        g.coord z
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w]
    exact congrFun ha ((reindexSymbolBasisIndex w ω e).symm z)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_slow_mul_inv_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ E A : F.RealPolynomialSymbolGroup w,
      F.SymbolSlowBound b ω hF w T (Real.exp (p + 2)) E →
      F.SymbolSlowBound b ω hF w T (Real.exp (p + 2)) A →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) := by
  obtain ⟨C, hC, hprod⟩ := exists_symbol_slow_product_bound s 1 2
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT E A hE hA
  have hinputs : ∀ x ∈ [E, A⁻¹], F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ 1)) x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa only [pow_one] using hE
    · simpa only [pow_one] using (F.symbolSlowBound_inv_iff b ω hF w T _ A).mpr hA
  simpa only [List.prod_cons, List.prod_nil, mul_one] using
    hprod F b ω hF w hw H p hH hp hι hσ hHp hc T hT [E, A⁻¹] (by simp) hinputs

theorem exists_symbol_rational_inv_mul_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ D R : F.RealPolynomialSymbolGroup w,
          F.SymbolRationalGrid b ω hF w l D → F.SymbolRationalGrid b ω hF w l R →
          F.SymbolRationalGrid b ω hF w m (D⁻¹ * R) := by
  obtain ⟨C, hC, hprod⟩ := exists_symbol_rational_product_bound s 2
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hprod F b ω hF w hw H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro D R hD hR
  have hinputs : ∀ x ∈ [D⁻¹, R], F.SymbolRationalGrid b ω hF w l x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact F.symbolRationalGrid_inv b ω hF w l hD
    · exact hR
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [D⁻¹, R] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

end

end OAI
