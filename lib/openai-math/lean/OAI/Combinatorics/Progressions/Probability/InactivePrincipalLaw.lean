import OAI.Combinatorics.Progressions.Estimates.InactiveAxisScale
import OAI.Combinatorics.Progressions.Polynomial.PrincipalMonomialScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def inactivePrincipalPMF (K q : ℕ) : PMF ℤ :=
  PMF.pure (inactivePrincipalCoefficient K q)

theorem inactivePrincipalPMF_support {K q : ℕ} {k : ℤ}
    (hk : k ∈ (inactivePrincipalPMF K q).support) : k = inactivePrincipalCoefficient K q := by
  simpa only [inactivePrincipalPMF, PMF.support_pure, Set.mem_singleton_iff] using hk

theorem inactivePrincipal_scaled_upper {h K q : ℕ} (hh : 0 < h) (hK : 0 < K) (hq : 0 < q) :
    |(inactivePrincipalCoefficient K q : ℝ)| * (inactiveSideLength h K q : ℝ) ^ h / K ≤ 1 / (q : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hlarge : 2 * q ≤ K
  · rw [inactivePrincipal_large hlarge, Int.cast_one, abs_one, one_mul]
    have hb : q * inactiveSideLength h K q ^ h ≤ K := by
      calc
        _ ≤ q * (K / q) := Nat.mul_le_mul_left q (inactiveSideLength_power hh hlarge)
        _ ≤ K := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self K q
    have hbr : (q : ℝ) * (inactiveSideLength h K q : ℝ) ^ h ≤ K := by exact_mod_cast hb
    apply (div_le_div_iff₀ hKr hqr).mpr
    nlinarith
  · rw [inactivePrincipal_small (lt_of_not_ge hlarge), Int.cast_zero, abs_zero, zero_mul, zero_div]
    positivity

theorem inactivePrincipal_scaled_lower {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) :
    1 / ((q : ℝ) * 2 ^ h) <
      |(inactivePrincipalCoefficient K q : ℝ)| * (inactiveSideLength h K q : ℝ) ^ h / K := by
  have hK : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [inactivePrincipal_large hlarge, Int.cast_one, abs_one, one_mul]
  have hb : (K : ℝ) < (q : ℝ) * 2 ^ h * (inactiveSideLength h K q : ℝ) ^ h := by
    exact_mod_cast inactiveSideLength_lower_power hh hq hlarge
  apply (div_lt_div_iff₀ (by positivity) hKr).mpr
  nlinarith

theorem inactivePrincipal_block_bound {V : Type*} {h K q : ℕ}
    (hh : 0 < h) (hK : 0 < K) (hq : 0 < q) (principal : Fin h → V) (T : V → ℝ)
    (hT : ∀ j, T (principal j) = (inactiveSideLength h K q : ℝ)) {k : ℤ}
    (hk : k ∈ (inactivePrincipalPMF K q).support) :
    |(k : ℝ) / K| * monomialScale T (productBlockExponent principal) ≤ 1 / (q : ℝ) := by
  rw [inactivePrincipalPMF_support hk, monomialScale_productBlockExponent]
  simp_rw [hT]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, abs_div,
    abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
  have hb := inactivePrincipal_scaled_upper hh hK hq
  convert hb using 1
  ring

noncomputable def inactiveDenominator (γ : ℝ) : ℕ := max 1 ⌈γ⁻¹⌉₊

theorem inactiveDenominator_pos (γ : ℝ) : 0 < inactiveDenominator γ :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

theorem inactiveDenominator_bound {γ : ℝ} (hγ : 0 < γ) : 1 / (inactiveDenominator γ : ℝ) ≤ γ := by
  have hq : (0 : ℝ) < inactiveDenominator γ := by exact_mod_cast inactiveDenominator_pos γ
  have hceil : γ⁻¹ ≤ (inactiveDenominator γ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈γ⁻¹⌉₊))
  have hb := mul_le_mul_of_nonneg_left hceil hγ.le
  rw [mul_inv_cancel₀ hγ.ne'] at hb
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hb)

end Erdos3

end

end OAI
