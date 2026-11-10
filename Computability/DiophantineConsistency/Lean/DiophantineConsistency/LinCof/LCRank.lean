import DiophantineConsistency.LinCof.LCEarlyFold
import DiophantineConsistency.LinCof.LCWindow
import DiophantineConsistency.P138.P138Rank

/-! # The signed rank for the linear cofactor: the main index is `R`

The linear-cofactor form of `P138Rank.main_index`, at a zero of the output with an index
modulus for the `k` slot (`LCWindow.IndexModulus`). After the early fold
(`LCEarlyFold.EarlyFold`) the main ordinate `|c| = ψ_b(idx)` has an odd index; this module
shows `idx = R` (`main_index`, packaged as the record `MainIndex`).

* `V = f² (c − R + 4 A U T) − c` with `f² = Df` is, up to the sign of `c`, the signed rank form
  of `TenPositiveSignedRankIndex.signed_rank_index` with `t = 0`, strong ordinate `I0 = c² u`
  and `rank = ±(R − c − 4 A U T)`; it gives `|rank| ≡ ±(2h+1) (mod |c|)`.
* `c ∣ U` (since `U = r c² Dm`), so `|rank| ≡ ±R (mod |c|)`.
* `TenPositivePellRankReduction.rank_to_main_index` (with `c² ∣ I0 = ψ_b(m)` and the transfer
  `|c| ≡ ±ψ_b(2h+1) (mod f)`) gives `|rank| ≡ ±idx (mod |c|)`.
* `2R < |c|` (from `|c| > |k|(|Y| − ½)`, `|k| ≥ R + 1`, `|Y| ≥ 3`) and `2 idx < ψ_b(idx) = |c|`
  give `idx = R` (`ArithmeticPellHalfIndex.sign_eq_of_half`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCSquares LCBudget LCAdjacent LCWindow
  LCEarlyFold
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open ZRowsCoprimeSquares (abs_eq_ι eq_or_eq_neg_abs)
open P138Adjacent (ι_pos)
open P138EarlyFold (pos_of_ι)
open P138Rank (sign_of_rank ι_absdiff three_le_of_odd)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Record
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **The main index.** -/
structure MainIndex (E : EarlyFold p x κ ω Λ ψ wt) where
  Rn : V
  hR : (𝓡).R = ι Rn
  hlo : |(𝓡).q| * ((𝓡).q ^ 2 - 1) < ι Rn
  hhi : ι Rn + 2 < (𝓡).q ^ 4
  hidx : E.idx = Rn
  hodd : Rn % 2 = 1
  hc : E.cn = ycoord Rn (E.Bn - 2)
  hDm : (𝓡).Dm = ι (xcoord Rn (E.Bn - 2)) * ι (xcoord Rn (E.Bn - 2))
  h2R : 2 * Rn < E.cn
  hRpos : 0 < Rn

end Record

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- `3 ≤ |Y|` from a positive budget. -/
theorem three_le_abs_Y (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    3 ≤ |(𝓡).Y| := by
  have h1 := abs_Y_ge ψ wt hp h hB
  have h2 : (3 : DiffRing V) ≤ 2 ^ 128 := by norm_num
  linarith

set_option maxHeartbeats 2000000 in
/-- **The main index is `R`.** -/
theorem main_index (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hκ : IndexModulus p x κ ω Λ ψ wt e) (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0)
    (E : EarlyFold p x κ ω Λ ψ wt) : Nonempty (MainIndex p x κ ω Λ ψ wt E) := by
  have hB : 0 < (𝓡).Budget := budget_pos ψ wt hp h hwt hz
  have hs := signs ψ wt hp h hB
  obtain ⟨Rn, hRn, hlo, hhi⟩ := window p x κ ω Λ ψ wt hp hs
  have hkR := k_ge ψ wt hp h hκ hB
  have hci := (c_interval ψ wt hp h hB).1
  have hY3 := three_le_abs_Y ψ wt hp h hB
  have hR0 : (0 : DiffRing V) ≤ ι Rn := ι_nonneg _
  -- `2 R < |c|`
  have h2R : 2 * Rn < E.cn := by
    apply ι_lt_ι.mp
    rw [map_mul, map_ofNat, ← E.hcn]
    have h5 : 5 * ((𝓡).R + 1) ≤ |(𝓡).k| * (2 * |(𝓡).Y| - 1) := by
      have := mul_le_mul hkR (show (5 : DiffRing V) ≤ 2 * |(𝓡).Y| - 1 by linarith)
        (by norm_num) (abs_nonneg _)
      linarith
    rw [hRn] at h5
    linarith
  have hRpos : 0 < Rn := by
    have : (0 : DiffRing V) ≤ |(𝓡).q| * ((𝓡).q ^ 2 - 1) := by
      have := abs_q_ge p x κ ω Λ ψ wt hp
      have h64 : (2 : DiffRing V) ≤ 2 ^ 64 := by norm_num
      have : 1 ≤ (𝓡).q ^ 2 := by rw [← sq_abs]; nlinarith
      exact mul_nonneg (abs_nonneg _) (by linarith)
    exact pos_of_ι (by linarith)
  have hcn0 := E.hcn0
  have hcnpos : (0 : DiffRing V) < ι E.cn := ι_pos hcn0
  have hidx3 : 3 ≤ E.idx :=
    three_le_of_odd E.hidx0 E.hidxodd (E.Bn - 2) E.hcidx
      (le_trans (le_trans (by norm_num) (mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hRpos)
        (by simp : (0 : V) ≤ 2))) h2R.le)
  have hJ2 : (2 : V) ≤ delta (E.Bn - 2) * E.I0 := by
    have h8 : (8 : V) ≤ delta (E.Bn - 2) :=
      ι_le_ι.mp (by rw [← E.hDelta, map_ofNat]; exact Delta_ge8 ψ wt hp h hB)
    have h1 : 1 ≤ E.I0 := pos_iff_one_le.mp E.hI0pos
    calc (2 : V) ≤ 8 := by norm_num
      _ ≤ delta (E.Bn - 2) := h8
      _ = delta (E.Bn - 2) * 1 := (mul_one _).symm
      _ ≤ delta (E.Bn - 2) * E.I0 := mul_le_mul_of_nonneg_left h1 (by simp)
  -- the signed rank residue
  have hfix : ∀ (xr rank : DiffRing V),
      xr = ι (E.f * E.f) * (ι (0 * E.cn) - rank) - ι E.cn → xr * xr = ι (E.vn * E.vn) →
      (ι E.cn : DiffRing V) ∣ rank - ι Rn ∨ (ι E.cn : DiffRing V) ∣ rank + ι Rn →
      SignMod E.cn Rn E.idx := by
    intro xr rank hx hxx hdiv
    obtain ⟨rp, rn, hrank, hmod⟩ :=
      TenPositiveSignedRankIndex.signed_rank_index E.cn E.f (delta (E.Bn - 2)) E.I0
        0 E.vn E.h xr rank hcn0 hJ2
        (dvd_trans (dvd_mul_right E.cn E.cn) E.hcdvd) E.hstrong hx hxx E.hsx
    have hres : SignMod E.cn (absdiff rp rn) Rn := by
      refine sign_of_rank hcn0 (r := rank) (by rw [ι_absdiff, hrank]) hdiv
    have hmain := TenPositivePellRankReduction.rank_to_main_index E.m (2 * E.h + 1) (E.Bn - 2)
      E.cn E.idx (absdiff rp rn) E.hm hidx3 E.hcidx (by rw [E.hmy]; exact E.hcdvd)
      (by rw [E.hmx]; exact E.hcsign) hmod
    exact sign_trans hcn0 (sign_symm hres) hmain
  have hVV : (𝓡).V * (𝓡).V = ι (E.vn * E.vn) := by rw [map_mul, ← E.hvn, abs_mul_abs_self]
  have hcdU : (ι E.cn : DiffRing V) ∣ x 8 → (ι E.cn : DiffRing V) ∣ (𝓡).U :=
    fun h' => by
      rw [U_eq]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow h' (by norm_num)) _) _
  have hsign : SignMod E.cn Rn E.idx := by
    rcases eq_or_eq_neg_abs (x 8) with h8 | h8 <;> rw [E.hcn] at h8
    · -- `c > 0`: `x = V`, `rank = R − c − 4 A U T`
      have hcU := hcdU (by rw [h8])
      refine hfix (𝓡).V ((𝓡).R - x 8 - 4 * (𝓡).A * (𝓡).U * x 7) ?_ hVV (Or.inl ?_)
      · rw [V_eq, E.hDf, map_mul, zero_mul, map_zero]; rw [h8]; ring
      · obtain ⟨u, hu⟩ := hcU
        exact ⟨-1 - 4 * (𝓡).A * u * x 7, by rw [hRn, hu, h8]; ring⟩
    · -- `c < 0`: `x = −V`, `rank = c − R + 4 A U T`
      have hcU := hcdU (by rw [h8]; exact dvd_neg.mpr (dvd_refl _))
      refine hfix (-(𝓡).V) (x 8 - (𝓡).R + 4 * (𝓡).A * (𝓡).U * x 7) ?_
        (by rw [neg_mul_neg]; exact hVV) (Or.inr ?_)
      · rw [V_eq, E.hDf, map_mul, zero_mul, map_zero]; rw [h8]; ring
      · obtain ⟨u, hu⟩ := hcU
        exact ⟨-1 + 4 * (𝓡).A * u * x 7, by rw [hRn, hu, h8]; ring⟩
  have h2i : 2 * E.idx < E.cn := by rw [E.hcidx]; exact twice_index_lt_y _ _ hidx3
  have heq : Rn = E.idx := sign_eq_of_half hRpos E.hidx0 h2R h2i hsign
  refine ⟨⟨Rn, hRn, hlo, hhi, heq.symm, by rw [heq]; exact E.hidxodd,
    by rw [heq]; exact E.hcidx, by rw [heq]; exact E.hDm, h2R, hRpos⟩⟩

end Regs

#print axioms three_le_abs_Y
#print axioms main_index

end DiophantineConsistency.LCRank
