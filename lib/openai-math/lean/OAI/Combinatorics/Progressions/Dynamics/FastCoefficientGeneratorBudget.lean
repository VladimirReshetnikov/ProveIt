import OAI.Combinatorics.Progressions.Estimates.BoundedFastCoefficientGenerators

namespace OAI

section

namespace Erdos3

theorem fastCoefficientGeneratorHeight_pos (n m r H : ℕ) (hH : 1 ≤ H) :
    0 < fastCoefficientGeneratorHeight n m r H := by
  have hHp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hB : 1 ≤ (n + 1) * H ^ n := Nat.succ_le_of_lt (by positivity)
  have hK := rationalKernelHeight_pos r hB
  unfold fastCoefficientGeneratorHeight fastKernelGeneratorHeight
  positivity

theorem fastKernelGeneratorHeight_le_exp (n m r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (fastKernelGeneratorHeight n m r H : ℝ) ≤ Real.exp ((p + 2) ^ 38) := by
  have hp1 : p ≤ (p + 2) ^ 1 := le_power_budget hp (by decide)
  have hB : (((n + 1) * H ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    exact rational_sum_cost_le_exp n H hp 1 1
      (hH.trans (Real.exp_le_exp.mpr hp1)) (hn.trans hp1)
  have hK : (rationalKernelHeight r ((n + 1) * H ^ n) : ℝ) ≤
      Real.exp ((p + 2) ^ 35) := by
    have hk := rationalKernelHeight_le_budget r ((n + 1) * H ^ n)
      (by positivity : 0 ≤ (p + 2) ^ 3)
      (hr.trans (le_power_budget hp (by decide : 1 ≤ 3))) hB
    exact exponential_budget_comp hp (by positivity) 3 7 le_rfl hk
  have hH' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 35) :=
    hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 35)))
  have hprod : ((rationalKernelHeight r ((n + 1) * H ^ n) * H : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 36) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 35) * Real.exp ((p + 2) ^ 35) :=
        mul_le_mul hK hH' (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (2 * (p + 2) ^ 35) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          2 * (p + 2) ^ 35 ≤ (p + 2) * (p + 2) ^ 35 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (p + 2) ^ 36 := by rw [pow_succ (p + 2) 35]; ring
  exact rational_sum_cost_le_exp m _ hp 36 1 hprod (hm.trans hp1)

theorem fastCoefficientGeneratorHeight_le_exp (n m r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (fastCoefficientGeneratorHeight n m r H : ℝ) ≤ Real.exp ((p + 2) ^ 40) :=
  rational_sum_cost_le_exp n _ hp 38 1
    (fastKernelGeneratorHeight_le_exp n m r H hp hn hm hr hH)
    (hn.trans (le_power_budget hp (by decide : 1 ≤ 1)))

namespace NilpotentLieFiltration

open Module

theorem exists_fast_coefficient_generators_exp
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 40) ∧
      ∃ z : κ → F.FirstCoefficientModule w,
        Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
        ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j) H' := by
  have he := F.exists_bounded_fast_coefficient_generators e ω hF w hw U v hspan hH hv
  obtain ⟨r, hr, z, hz, hzh⟩ := he
  refine ⟨_, fastCoefficientGeneratorHeight_pos _ _ _ _ hH, ?_, z, hz, hzh⟩
  exact fastCoefficientGeneratorHeight_le_exp _ _ _ _ hp hn hm
    ((Nat.cast_le.mpr hr).trans hq) hHp

end NilpotentLieFiltration
end Erdos3

end

end OAI
