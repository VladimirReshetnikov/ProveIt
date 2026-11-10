import DiophantineConsistency.P138.P138EarlyFold
import DiophantineConsistency.P138.P138Window
import DiophantineConsistency.BFS943.PellRankReduction

/-! # The signed rank: the main index is `R`

132-lowops §5, first paragraph, at a zero of the output with an index modulus for the `k`
slot (`P138Window.IndexModulus`; native 924/107 and short 840/108 alike). After the early fold
(`P138EarlyFold.EarlyFold`) the main ordinate `|c| = ψ_b(p)` has an odd index `p`; this module
shows `p = R` (`main_index`, packaged as the record `MainIndex`).

* The actual residues: `V = f² (c − R + 4 U BP T) − c` with `f² = Df` is, up to the sign of `c`,
  the signed rank form of `TenPositiveSignedRankIndex.signed_rank_index` with `t = 0` and
  `rank = ±(R − c − 4 U BP T)`; it gives `|rank| ≡ ±(2h+1) (mod |c|)`.
* `c ∣ U` (since `U = A r c²`), so `|rank| ≡ ±R (mod |c|)` (`sign_of_rank`).
* `TenPositivePellRankReduction.rank_to_main_index` (with `c² ∣ I0 = ψ_b(m)` and the transfer
  `|c| ≡ ±ψ_b(2h+1) (mod f)`) gives `|rank| ≡ ±p (mod |c|)`.
* `2R < |c|` (from `|c| > |k|(|Y| − ½)`, `|k| ≥ R + 1`) and `2p < ψ_b(p) = |c|` give `p = R`
  (`ArithmeticPellHalfIndex.sign_eq_of_half`).

The first index, the projector and the orientation are not used.

The module ends with the record `Folded`: the facts about front registers that the rest of the
chain needs (`folded_of_zero`). From there on the chain does not read the zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Rank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold
open ArithmeticPellRecurrence ArithmeticPellHalfIndex

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Signed residues in `DiffRing V` -/

theorem mod_eq_of_ι_dvd {m a b : V} (hm : 0 < m) (hd : (ι m : DiffRing V) ∣ ι a - ι b) :
    a % m = b % m := by
  obtain ⟨t, ht⟩ := hd
  rcases nonneg_or_nonpos t with ⟨w, hw⟩ | ⟨w, hw⟩
  · have he : a = b + m * w := by
      apply ι_injective
      rw [map_add, map_mul]; linear_combination ht + ι m * hw
    rw [he, mod_add_mul' _ _ hm]
  · have he : a + m * w = b := by
      apply ι_injective
      rw [map_add, map_mul]; linear_combination ht + ι m * hw
    have h : (a + m * w) % m = b % m := by rw [he]
    rwa [mod_add_mul' _ _ hm] at h

theorem ι_dvd_of_mod_eq {m a b : V} (h : a % m = b % m) :
    (ι m : DiffRing V) ∣ ι a - ι b := by
  have ha := div_add_mod a m
  have hb := div_add_mod b m
  refine ⟨ι (a / m) - ι (b / m), ?_⟩
  have ha' := congrArg (ι (V := V)) ha
  have hb' := congrArg (ι (V := V)) hb
  simp only [map_add, map_mul] at ha' hb'
  rw [h] at ha'
  linear_combination hb' - ha'

theorem sign_of_dvd {m a b : V} (hm : 0 < m)
    (h : (ι m : DiffRing V) ∣ ι a - ι b ∨ (ι m : DiffRing V) ∣ ι a + ι b) : SignMod m a b := by
  rcases h with h | h
  · exact Or.inl (mod_eq_of_ι_dvd hm h)
  · right
    rw [← map_add] at h
    exact mod_eq_zero_iff_dvd.mpr (ι_dvd_iff.mp h)

/-- A rank `r` whose magnitude is `a`, congruent to `±b` modulo `m`. -/
theorem sign_of_rank {m a b : V} {r : DiffRing V} (hm : 0 < m) (ha : |r| = ι a)
    (h : (ι m : DiffRing V) ∣ r - ι b ∨ (ι m : DiffRing V) ∣ r + ι b) : SignMod m a b := by
  apply sign_of_dvd hm
  rcases eq_or_eq_neg_abs r with hr | hr <;> rw [ha] at hr <;> rw [hr] at h
  · exact h
  · rcases h with h | h
    · right; have := dvd_neg.mpr h; rwa [show -(-ι a - ι b) = ι a + ι b by ring] at this
    · left; have := dvd_neg.mpr h; rwa [show -(-ι a + ι b) = ι a - ι b by ring] at this

theorem ι_absdiff (a b : V) : (ι (absdiff a b) : DiffRing V) = |ι a - ι b| := by
  unfold absdiff
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, ι_tsub' h, abs_of_nonpos (by linarith [ι_le_ι.mpr h])]
    ring
  · rw [tsub_eq_zero_of_le h, add_zero, ι_tsub' h, abs_of_nonneg (by linarith [ι_le_ι.mpr h])]

theorem three_le_of_odd {i c : V} (hi : 0 < i) (hodd : i % 2 = 1) (b : V) (hc : c = ycoord i b)
    (hc2 : 2 ≤ c) : 3 ≤ i := by
  have hr1 : 1 < i := by
    by_contra hn
    have hle : i ≤ 1 := le_of_not_gt hn
    have hone : i = 1 := le_antisymm hle (pos_iff_one_le.mp hi)
    have hy1 : ycoord 1 b = 1 := by simpa using y_succ (0 : V) b
    rw [hone, hy1] at hc
    rw [hc] at hc2
    exact absurd hc2 (by norm_num)
  have hr2 : 2 ≤ i := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hr1
  have hr2lt : 2 < i := by
    rcases lt_or_eq_of_le hr2 with h | h
    · exact h
    · rw [← h] at hodd; simp at hodd
  simpa only [show (2 : V) + 1 = 3 by norm_num] using lt_iff_succ_le.mp hr2lt

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK p x κ

/-- The signs of the centered budget, from a positive budget. -/
theorem signs_of_budget (hp : PortFacts p) (hB : 0 < (𝓡).Budget) :
    0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q := by
  obtain ⟨_, _, _, h1, h2, h3, _⟩ := centered p x κ hp hB
  exact ⟨h1, h2, h3⟩

/-- The signs of the centered budget at a zero. -/
theorem signs (hp : PortFacts p) (hz : valueK p x κ = 0) :
    0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q :=
  signs_of_budget p x κ hp (by linarith [budget_ge p x κ hp hz])

theorem three_le_abs_Y (hp : PortFacts p) : 3 ≤ |(𝓡).Y| := by
  have hq := abs_q_ge p x κ hp
  have h64 : (3 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have hq3 : |(𝓡).q| ≤ |(𝓡).q| ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  linarith [abs_Y p x κ hp]

/-- **The main index.** -/
structure MainIndex (E : EarlyFold p x κ) where
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

set_option maxHeartbeats 2000000 in
theorem main_index (hp : PortFacts p) (hκ : IndexModulus p x κ) (hz : valueK p x κ = 0)
    (E : EarlyFold p x κ) : Nonempty (MainIndex p x κ E) := by
  have hB : 0 < (𝓡).Budget := by linarith [budget_ge p x κ hp hz]
  have hs := signs p x κ hp hz
  obtain ⟨Rn, hRn, hlo, hhi⟩ := window p x κ hp hs
  have hkR := k_ge p x κ hp hκ hs
  have hci := (c_interval p x κ hp hB).1
  have hY3 := three_le_abs_Y p x κ hp
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
      have := abs_q_ge p x κ hp
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
  -- the signed rank residue
  have hfix : ∀ (xr rank : DiffRing V),
      xr = ι (E.f * E.f) * (ι (0 * E.cn) - rank) - ι E.cn → xr * xr = ι (E.vn * E.vn) →
      (ι E.cn : DiffRing V) ∣ rank - ι Rn ∨ (ι E.cn : DiffRing V) ∣ rank + ι Rn →
      SignMod E.cn Rn E.idx := by
    intro xr rank hx hxx hdiv
    obtain ⟨rp, rn, hrank, hmod⟩ :=
      TenPositiveSignedRankIndex.signed_rank_index E.cn E.f (delta (E.Bn - 2)) (E.Un * E.p0)
        0 E.vn E.h xr rank hcn0
        (by
          have h8 : (8 : V) ≤ delta (E.Bn - 2) :=
            ι_le_ι.mp (by rw [← E.hDelta, map_ofNat]; exact Delta_gt p x κ hp)
          have h1 : 1 ≤ E.Un * E.p0 := pos_iff_one_le.mp (mul_pos E.hUn0 E.hp0)
          calc (2 : V) ≤ 8 := by norm_num
            _ ≤ delta (E.Bn - 2) := h8
            _ = delta (E.Bn - 2) * 1 := (mul_one _).symm
            _ ≤ delta (E.Bn - 2) * (E.Un * E.p0) := mul_le_mul_of_nonneg_left h1 (by simp))
        (dvd_trans (dvd_mul_right E.cn E.cn) E.hcdvd) E.hstrong hx hxx E.hsx
    have hres : SignMod E.cn (absdiff rp rn) Rn := by
      refine sign_of_rank hcn0 (r := rank) (by rw [ι_absdiff, hrank]) hdiv
    have hmain := TenPositivePellRankReduction.rank_to_main_index E.m (2 * E.h + 1) (E.Bn - 2)
      E.cn E.idx (absdiff rp rn) E.hm hidx3 E.hcidx (by rw [E.hmy]; exact E.hcdvd)
      (by rw [E.hmx]; exact E.hcsign) hmod
    exact sign_trans hcn0 (sign_symm hres) hmain
  have hVV : (𝓡).V * (𝓡).V = ι (E.vn * E.vn) := by rw [map_mul, ← E.hvn, abs_mul_abs_self]
  have hcdU : (ι E.cn : DiffRing V) ∣ x 8 → (ι E.cn : DiffRing V) ∣ (𝓡).U :=
    fun h => by rw [U_eq]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _
  have hsign : SignMod E.cn Rn E.idx := by
    rcases eq_or_eq_neg_abs (x 8) with h8 | h8 <;> rw [E.hcn] at h8
    · -- `c > 0`: `x = V`, `rank = R − c − 4 U BP T`
      have hcU := hcdU (by rw [h8])
      refine hfix (𝓡).V ((𝓡).R - x 8 - 4 * (𝓡).U * (𝓡).BP * x 7) ?_ hVV (Or.inl ?_)
      · rw [V_eq, E.hDf, map_mul, zero_mul, map_zero]; rw [h8]; ring
      · obtain ⟨u, hu⟩ := hcU
        exact ⟨-1 - 4 * u * (𝓡).BP * x 7, by rw [hRn, hu, h8]; ring⟩
    · -- `c < 0`: `x = −V`, `rank = c − R + 4 U BP T`
      have hcU := hcdU (by rw [h8]; exact dvd_neg.mpr (dvd_refl _))
      refine hfix (-(𝓡).V) (x 8 - (𝓡).R + 4 * (𝓡).U * (𝓡).BP * x 7) ?_
        (by rw [neg_mul_neg]; exact hVV) (Or.inr ?_)
      · rw [V_eq, E.hDf, map_mul, zero_mul, map_zero]; rw [h8]; ring
      · obtain ⟨u, hu⟩ := hcU
        exact ⟨-1 + 4 * u * (𝓡).BP * x 7, by rw [hRn, hu, h8]; ring⟩
  have h2i : 2 * E.idx < E.cn := by rw [E.hcidx]; exact twice_index_lt_y _ _ hidx3
  have heq : Rn = E.idx := sign_eq_of_half hRpos E.hidx0 h2R h2i hsign
  refine ⟨⟨Rn, hRn, hlo, hhi, heq.symm, by rw [heq]; exact E.hidxodd,
    by rw [heq]; exact E.hcidx, by rw [heq]; exact E.hDm, h2R, hRpos⟩⟩

/-! ## The folded front

Everything the rest of the soundness chain (`P138FirstIndex` … `P138Leaf`) reads from a zero.
Every field is a statement about front registers of `P138Value.regsK` (`A, c, Budget, Dt, H,
Kq, R, Dm`); the back end of the circuit (`U, BP, strong, Df, Q, V, Z, RG, …`) does not occur.
A circuit with the same front and a different back end (package 131's two-root 810/112) reuses
the chain by building this record from its own zero. -/

/-- **The folded front**: the main Pell pair `|c| = ψ_b(R)`, `b = |A| − 2`, with odd index
`R`, a positive budget, the first norm `Dt = τ²` and `H ∣ Kq⁵`. -/
structure Folded where
  Bn : V
  cn : V
  Rn : V
  τ : V
  hBn : |(𝓡).A| = ι Bn
  hB3 : 3 ≤ Bn
  hcn : |x 8| = ι cn
  hcn0 : 0 < cn
  hbudget : 0 < (𝓡).Budget
  hDt : (𝓡).Dt = ι τ * ι τ
  hHK : (𝓡).H ∣ Kq p x κ ^ 5
  hR : (𝓡).R = ι Rn
  hodd : Rn % 2 = 1
  hc : cn = ycoord Rn (Bn - 2)
  hDm : (𝓡).Dm = ι (xcoord Rn (Bn - 2)) * ι (xcoord Rn (Bn - 2))
  hRpos : 0 < Rn

/-- **A zero of package 138's output gives the folded front.** -/
theorem folded_of_zero (hp : PortFacts p) (hκ : IndexModulus p x κ) (hz : valueK p x κ = 0) :
    Nonempty (Folded p x κ) := by
  obtain ⟨E⟩ := early_fold p x κ hp hz
  obtain ⟨M⟩ := main_index p x κ hp hκ hz E
  obtain ⟨τ, _, _, _, hDt, _, _⟩ := guard_split p x κ hp hz E
  exact ⟨⟨E.Bn, E.cn, M.Rn, τ, E.hBn, E.hB3, E.hcn, E.hcn0,
    by linarith [budget_ge p x κ hp hz], hDt, H_dvd_Kq5 p x κ hp hz E, M.hR, M.hodd, M.hc,
    M.hDm, M.hRpos⟩⟩

end Regs

#print axioms mod_eq_of_ι_dvd
#print axioms sign_of_rank
#print axioms ι_absdiff
#print axioms main_index
#print axioms folded_of_zero

end DiophantineConsistency.P138Rank
