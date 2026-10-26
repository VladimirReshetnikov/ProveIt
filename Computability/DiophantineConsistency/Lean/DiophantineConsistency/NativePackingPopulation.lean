import DiophantineConsistency.NativeMaskPopulation

/-! Exact converse population calculation from two successful native masks.
All block bounds are proved before binary populations are split. -/

namespace DiophantineConsistency.NativePackingPopulation

open Jones1982
set_option Elab.async false

/-- Disjoint binary words below one window have an ordinary sum below it. -/
theorem disjoint_add_lt {u A M : ℕ} (hA : A < 2^u) (hM : M < 2^u)
    (hm : A &&& M = 0) : A+M < 2^u := by
  have he := JM1984.add_eq_land_add_lor A M
  rw [hm,zero_add] at he
  rw [he]
  exact Nat.or_lt_two_pow hA hM

/-- The top block is unrestricted; all lower blocks are strict representatives. -/
theorem four_block_exact {u A B C : ℕ} (D : ℕ)
    (hA : A < 2^u) (hB : B < 2^u) (hC : C < 2^u) :
    σ 2 (A+2^u*B+(2^u)^2*C+(2^u)^3*D) =
      σ 2 A+σ 2 B+σ 2 C+σ 2 D := by
  have he : A+2^u*B+(2^u)^2*C+(2^u)^3*D =
      ((D*2^u+C)*2^u+B)*2^u+A := by ring
  rw [he,lemma_2_5 hA,lemma_2_5 hB,lemma_2_5 hC]
  omega

/-- Successful masks give the exact population; no lower bound from a
Pell source or already calibrated population is assumed. -/
theorem mask_population {u A F M H : ℕ}
    (hA : A < 2^u) (hF : F < 2^u) (hM : M < 2^u) (hH : H < 2^u)
    (hmA : A &&& M = 0) (hmF : F &&& H = 0) :
    σ 2 ((A+M)+2^u*(F+H)+(2^u)^2*(2^u-1-A)+
      (2^u)^3*(2^u-1-F)) = 2*u+σ 2 M+σ 2 H := by
  have hq : 0 < 2^u := Nat.two_pow_pos _
  have hpacked := four_block_exact (2^u-1-F)
    (disjoint_add_lt hA hM hmA) (disjoint_add_lt hF hH hmF)
    (by omega : 2^u-1-A < 2^u)
  have hAM := lemma_2_2 A M
  have hFH := lemma_2_2 F H
  rw [(τ_two_eq_zero_iff A M).mpr hmA,zero_add] at hAM
  rw [(τ_two_eq_zero_iff F H).mpr hmF,zero_add] at hFH
  have hCA := lemma_2_6 hA
  have hCF := lemma_2_6 hF
  omega

theorem calibrated_population {u A F M H : ℕ}
    (hA : A < 2^u) (hF : F < 2^u) (hM : M < 2^u) (hH : H < 2^u)
    (hmA : A &&& M = 0) (hmF : F &&& H = 0)
    (hpop : σ 2 M+σ 2 H = u+2) :
    σ 2 ((A+M)+2^u*(F+H)+(2^u)^2*(2^u-1-A)+
      (2^u)^3*(2^u-1-F)) = 3*u+2 := by
  rw [mask_population hA hF hM hH hmA hmF]
  omega

end DiophantineConsistency.NativePackingPopulation
