import DiophantineConsistency.Nine121.N105Prefix
import DiophantineConsistency.Nine121.N101Contract

/-! # Package 105's H1868 prefix contract in every model of `𝗜𝚺₁`

At the wang943-mixed-121x8801 ports `pR = portsR Mixed121Ports.ports`, for the H1868 layout
(`N105Layout`, `N105Prefix`; `N₀ = B¹¹⁷`, `L = 2bB¹⁹⁸⁶`, `N = 2^16012032 B¹⁰⁵⁵`, `t = bB¹¹⁶`):

* `prefix_naturals`: for every model natural `b > 0` and `g`, the prefix registers `R, N, t`
  are images of model naturals with `R, N ≥ 8`, `b ≤ R, N`, `t > 0`;
* `contract`: for `b = 2ᵏ` and `g < 4t`,
  `N² ∣ C(2R, R) ↔ ∃ z, (∀ i, zᵢ < b) ∧ g = Σᵢ zᵢ B^{wᵢ} ∧ ∀ r, ρ_r(z + 1) = 0`, with `ρ` the
  gapN86 rows (`N101Source.rows`); the population is now `σ(T_c) = 139v − 31k − 22`;
* `code_of_source`: a positive parent zero gives `k`, a digit vector `z` with `zᵢ < 2ᵏ`, a
  positive `g = Σ zᵢ B^{wᵢ} < bB¹¹⁶` and vanishing gapN86 rows at `z + 1`.

The way back from the code to the parent source is layout-free: `N101Contract.source_of_code`.
Everything that does not depend on the layout (the port bounds `N101Contract.port_facts`, the
scales, `Bm`, `v_facts`) is reused from `N101Contract`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N105Contract
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelDigitTransfer ModelCarries ArithmeticBinaryCarry
open N105Layout N105Prefix
open N101Prefix (Bq scale_facts pow_step sum_range_table)
open N101Contract (Hc port_facts Bm ι_Bm hBb exp_ge_eight thresholdScale_eq one_le_ι v_facts
  exp_mul_lit exp_one')
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-! ## The prefix registers are model naturals -/

theorem prefix_pos (b g : V) (hb : 0 < b) :
    0 < Gs pR (ι b) (ι g) ∧ 0 ≤ maskq (ι b) ∧ 0 ≤ Tcq (ι b) ∧ 0 ≤ Scq pR (ι b) (ι g) ∧
      Lq (ι b) - 1 ≤ Rq pR (ι b) (ι g) ∧ 8 ≤ Lq (ι b) - 1 ∧ ι b ≤ Lq (ι b) - 1 ∧
      8 ≤ Nq (ι b) ∧ ι b ≤ Nq (ι b) ∧ 0 < tq (ι b) := by
  obtain ⟨hH8, hc⟩ := port_facts (V := V)
  have hb1 := one_le_ι hb
  have hBb' := hBb b
  obtain ⟨hB32, -, hBb4, hbb⟩ := scale_facts (ι b) Hc hb1 hH8 hBb'
  have hB1 : (1 : DiffRing V) ≤ Bq (ι b) := by linarith
  have hB0 : (0 : DiffRing V) ≤ Bq (ι b) := by linarith
  have hP : ∀ n, (0 : DiffRing V) ≤ Bq (ι b) ^ n := fun n => pow_nonneg hB0 n
  have hg0 := ι_nonneg g
  have hl0 := ell_nonneg (ι b) hB0
  have hl := ell_le (ι b) hB1
  have hT0 := Tst_nonneg (ι b) hB0
  have hG := Gs_pos pR (ι b) (ι g) Hc hb1 hH8 hBb' hc (by rw [Ust]; linarith [ell_ge (ι b) hB0])
  -- the mask is nonnegative
  have hm : 0 ≤ maskq (ι b) := by
    rw [maskq, N0, pow_succ']
    have a1 : ell (ι b) * (ι b - 1) ≤ 31 * Bq (ι b) ^ 116 * ι b :=
      mul_le_mul hl (by linarith) (by linarith) (by linarith [hP 116])
    have a2 : 4096 * (ι b * ι b) * Bq (ι b) ^ 116 ≤ Bq (ι b) * Bq (ι b) ^ 116 :=
      mul_le_mul_of_nonneg_right hBb4 (hP 116)
    have a3 : 31 * Bq (ι b) ^ 116 * ι b ≤ 31 * (ι b * ι b) * Bq (ι b) ^ 116 := by
      have := mul_le_mul_of_nonneg_right hbb (hP 116); linarith
    have a4 : (1 : DiffRing V) ≤ (ι b * ι b) * Bq (ι b) ^ 116 :=
      le_trans (le_trans hb1 hbb) (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
    linarith
  have hTc : 0 ≤ Tcq (ι b) := by
    rw [Tcq]
    have := mul_nonneg (pow_nonneg hB0 117) (mul_nonneg hT0 (by linarith : (0 : DiffRing V) ≤ Bq (ι b) - 2))
    unfold N0; linarith
  have hSc : 0 ≤ Scq pR (ι b) (ι g) := by
    rw [Scq]
    have := mul_nonneg (pow_nonneg hB0 117) (by linarith : (0 : DiffRing V) ≤ Tst (ι b) + 2 * Gs pR (ι b) (ι g))
    unfold N0; linarith
  have hLb : Bq (ι b) ≤ Bq (ι b) ^ 1986 := by
    have := pow_step _ hB1 1 1986 (by norm_num); rwa [pow_one] at this
  have hL1 : 2 * ι b * Bq (ι b) ≤ Lq (ι b) := by
    rw [Lq]; exact mul_le_mul_of_nonneg_left hLb (by linarith)
  have hbB : 32768 * ι b ≤ 2 * ι b * Bq (ι b) := by
    have := mul_le_mul_of_nonneg_left hB32 (by linarith : (0 : DiffRing V) ≤ ι b); linarith
  have hR : Lq (ι b) - 1 ≤ Rq pR (ι b) (ι g) := by
    rw [Rq]
    have : 0 ≤ (Lq (ι b) - 1) * (Tcq (ι b) + Scq pR (ι b) (ι g)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hN8 : (8 : DiffRing V) ≤ ι (Exp.exp (16012032 : V)) := exp_ge_eight (by norm_num)
  have hB1055 : Bq (ι b) ≤ Bq (ι b) ^ 1055 := by
    have := pow_step _ hB1 1 1055 (by norm_num); rwa [pow_one] at this
  have hN : 8 * Bq (ι b) ≤ Nq (ι b) := by
    rw [Nq, thresholdScale_eq]
    exact mul_le_mul hN8 hB1055 hB0 (by linarith)
  have ht : 0 < tq (ι b) := mul_pos (by linarith) (pow_pos (by linarith) _)
  refine ⟨hG, hm, hTc, hSc, hR, by linarith, by linarith, by linarith, by linarith, ht⟩

/-- **The prefix registers are model naturals**, with the finalizer's size hypotheses. -/
theorem prefix_naturals (b g : V) (hb : 0 < b) :
    ∃ R N t : V, ι R = Rq pR (ι b) (ι g) ∧ ι N = Nq (ι b) ∧ ι t = tq (ι b) ∧
      8 ≤ R ∧ 8 ≤ N ∧ b ≤ R ∧ b ≤ N ∧ 0 < t := by
  obtain ⟨-, -, -, -, hR, hR8, hRb, hN8, hNb, ht⟩ := prefix_pos b g hb
  obtain ⟨R, hRe⟩ := nonneg_iff.mp (by linarith : (0 : DiffRing V) ≤ Rq pR (ι b) (ι g))
  obtain ⟨N, hNe⟩ := nonneg_iff.mp (by linarith : (0 : DiffRing V) ≤ Nq (ι b))
  obtain ⟨t, hte⟩ := nonneg_iff.mp ht.le
  refine ⟨R, N, t, hRe.symm, hNe.symm, hte.symm, ?_, ?_, ?_, ?_, ?_⟩
  · apply ι_le_ι.mp; rw [map_ofNat, ← hRe]; linarith
  · apply ι_le_ι.mp; rw [map_ofNat, ← hNe]; linarith
  · apply ι_le_ι.mp; rw [← hRe]; linarith
  · apply ι_le_ι.mp; rw [← hNe]; linarith
  · apply ι_lt_ι.mp; rw [map_zero, ← hte]; exact ht

/-! ## The high block -/

/-- `T*` as a model natural. -/
def TstN (B : V) : V := ∑ r, B ^ targets r

/-- The high target mask `Σ_{targets} (B − 2) Bᵉ`. -/
def highMask (B : V) : V := dsum B (fun e => if LowMask.Pos targets e then B - 2 else 0) 1869

/-- The low code mask. -/
def lowMask (b B : V) : V := dsum B (codeMask b B (LowMask.Pos weights)) 117

theorem ι_TstN (b : V) : ι (TstN (Bm b)) = Tst (ι b) := by
  simp only [TstN, map_sum, map_pow, ι_Bm, Tst]

theorem targets_lt : ∀ r, targets r < 1869 := fun r => lt_of_le_of_lt (targets_le r) (by norm_num)
theorem weights_lt : ∀ i, weights i < 117 := fun i => lt_of_le_of_lt (weights_le i) (by norm_num)

theorem highMask_eq (B : V) : highMask B = ∑ r, (B - 2) * B ^ targets r := by
  rw [highMask, LowMask.dsum_weights B targets targets_injective 1869 targets_lt]
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [if_pos ⟨r, rfl⟩]
  · intro j _ hp; rw [if_neg hp]

theorem ι_highMask (b : V) (hB : 2 ≤ Bm b) :
    ι (highMask (Bm b)) = Tst (ι b) * (Bq (ι b) - 2) := by
  rw [highMask_eq, map_sum, Tst, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_mul, P72Root.ι_tsub hB, map_pow, ι_Bm, map_ofNat]; ring

theorem lowMask_dsum (k v : V) (hkv : k ≤ v) :
    lowMask (Exp.exp k) (Exp.exp v) + (Exp.exp k - 1) * ∑ i, Exp.exp v ^ weights i + 1 =
      Exp.exp v ^ 117 := by
  have h := codeMask_dsum (one_le_exp k) (exp_monotone_le.2 hkv) (LowMask.Pos weights) 117
  have hd : dsum (Exp.exp v) (codeInd (LowMask.Pos weights)) 117 = ∑ i, Exp.exp v ^ weights i := by
    rw [LowMask.dsum_weights _ weights weights_injective 117 weights_lt]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [codeInd, if_pos ⟨i, rfl⟩, one_mul]
    · intro j _ hp; rw [codeInd, if_neg hp]
  rw [← hd]; exact h

/-- **The high block**: for a digit vector `z < b` packed in `g`, no carry against the high
target mask iff every gapN86 row vanishes at `z + 1`. -/
theorem high_iff (k : V) (z : Fin 31 → V) (hz : ∀ i, z i < Exp.exp k) (G : V)
    (hG : ι G = Gs pR (ι (Exp.exp k)) (ι (∑ i, z i * Bm (Exp.exp k) ^ weights i))) :
    NoCarry (TstN (Bm (Exp.exp k)) + 2 * G) (highMask (Bm (Exp.exp k))) ↔
      ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  obtain ⟨hH8, hc⟩ := port_facts (V := V)
  obtain ⟨v, hv⟩ : ∃ v : V, v = 2134939 + k + k := ⟨_, rfl⟩
  obtain ⟨-, hv1, hBm⟩ := v_facts k v hv
  have hb1 : (1 : DiffRing V) ≤ ι (Exp.exp k) := one_le_ι (exp_pos k)
  have hBv : ι (Exp.exp v) = Bq (ι (Exp.exp k)) := by rw [← hBm, ι_Bm]
  have hu : Ust (ι (Exp.exp k)) (ι (∑ i, z i * Bm (Exp.exp k) ^ weights i)) =
      ∑ i, (fun i => ι (z i + 1)) i * Bq (ι (Exp.exp k)) ^ weights i := by
    rw [Ust, ell, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, map_pow, ι_Bm, map_add, map_one]; ring
  have hcb : ∀ e < 1869,
      4 * |(sourcePoly pR (fun i => ι (z i + 1))).coeff e| + 4 ≤ ι (Exp.exp v) := by
    intro e _
    rw [hBv]
    refine coeff_bound pR _ Hc hb1 hH8 (hBb _) hc _ (fun i => ι_nonneg _) (fun i => ?_) e
    exact ι_le_ι.2 (lt_iff_succ_le.mp (hz i))
  have hT : Tst (ι (Exp.exp k)) = ∑ e ∈ Finset.range 1869,
      (if LowMask.Pos targets e then (1 : DiffRing V) else 0) * Bq (ι (Exp.exp k)) ^ e := by
    rw [Tst, sum_range_table targets targets_injective 1869 targets_lt]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [if_pos ⟨r, rfl⟩, one_mul]
    · intro j _ hp
      rw [if_neg (fun ⟨r, hr⟩ => hp r hr), zero_mul]
  have hX : ι (TstN (Bm (Exp.exp k)) + 2 * G) =
      ∑ e ∈ Finset.range 1869,
        (2 * (sourcePoly pR (fun i => ι (z i + 1))).coeff e +
          if LowMask.Pos targets e then 1 else 0) * ι (Exp.exp v) ^ e := by
    rw [map_add, map_mul, map_ofNat, ι_TstN, hG, Gs_sum pR _ _ _ hu, hBv, hT, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have key := SignedDigits.high_noCarry_iff v hv1 1869 (LowMask.Pos targets)
    (fun e => (sourcePoly pR (fun i => ι (z i + 1))).coeff e) hcb _ hX
  have hmask : highMask (Bm (Exp.exp k)) =
      dsum (Exp.exp v) (fun e => if LowMask.Pos targets e then Exp.exp v - 2 else 0) 1869 := by
    rw [hBm, highMask]
  rw [hmask, key]
  constructor
  · intro h r
    have h0 : (sourcePoly pR (fun i => ι (z i + 1))).coeff (targets r) = 0 :=
      h _ (targets_lt r) ⟨r, rfl⟩
    rw [coeff_target] at h0
    exact (mul_eq_zero.mp h0).resolve_left two_ne_zero
  · rintro h e _ ⟨r, rfl⟩
    show (sourcePoly pR (fun i => ι (z i + 1))).coeff (targets r) = 0
    rw [coeff_target, h r, mul_zero]

/-! ## The calibration and the contract -/

theorem pop_low (k v : V) (hkv : k ≤ v) :
    ArithmeticBinaryPopulation.population (lowMask (Exp.exp k) (Exp.exp v)) + 31 * k = 117 * v := by
  have hdig : ∀ j < 117, codeMask (Exp.exp k) (Exp.exp v) (LowMask.Pos weights) j < Exp.exp v := by
    intro j _
    unfold codeMask
    split_ifs
    · exact tsub_lt_self (exp_pos v) (exp_pos k)
    · exact tsub_lt_self (exp_pos v) one_pos
  rw [lowMask, DigitPopulation.population_dsum v _ 117 hdig]
  have key : ∀ j, ArithmeticBinaryPopulation.population
      (codeMask (Exp.exp k) (Exp.exp v) (LowMask.Pos weights) j) +
      (if LowMask.Pos weights j then k else 0) = v := by
    intro j
    unfold codeMask
    split_ifs
    · rw [DigitPopulation.population_exp_sub_exp hkv, tsub_add_cancel_of_le hkv]
    · rw [ArithmeticBinaryPopulation.population_exp_sub_one, add_zero]
  have hk : ∑ j ∈ Finset.range 117, (if LowMask.Pos weights j then k else 0) = 31 * k := by
    rw [sum_range_table weights weights_injective 117 weights_lt]
    · rw [Finset.sum_congr rfl (fun i _ => if_pos (show LowMask.Pos weights (weights i) from ⟨i, rfl⟩))]
      simp
    · intro j _ hp; rw [if_neg (fun ⟨i, hi⟩ => hp i hi)]
  have h3 : ∑ j ∈ Finset.range 117, (ArithmeticBinaryPopulation.population
      (codeMask (Exp.exp k) (Exp.exp v) (LowMask.Pos weights) j) +
      (if LowMask.Pos weights j then k else 0)) = 117 * v := by
    rw [Finset.sum_congr rfl (fun j _ => key j)]; simp
  rw [Finset.sum_add_distrib, hk] at h3
  exact h3

theorem pop_high (v : V) (hv : 1 ≤ v) :
    ArithmeticBinaryPopulation.population (highMask (Exp.exp v)) + 22 = 22 * v := by
  have hdig : ∀ j < 1869, (fun e => if LowMask.Pos targets e then Exp.exp v - 2 else 0) j <
      Exp.exp v := by
    intro j _
    dsimp only
    split_ifs
    · exact tsub_lt_self (exp_pos v) (by norm_num)
    · exact exp_pos v
  rw [highMask, DigitPopulation.population_dsum v _ 1869 hdig]
  have h2 : Exp.exp v - 2 = Exp.exp v - Exp.exp 1 := by rw [exp_one']
  have key : ∀ j, ArithmeticBinaryPopulation.population
      (if LowMask.Pos targets j then Exp.exp v - 2 else 0) +
      (if LowMask.Pos targets j then 1 else 0) = if LowMask.Pos targets j then v else 0 := by
    intro j
    split_ifs
    · rw [h2, DigitPopulation.population_exp_sub_exp hv, tsub_add_cancel_of_le hv]
    · rw [DigitPopulation.population_zero, add_zero]
  have hk : ∀ a : V, ∑ j ∈ Finset.range 1869, (if LowMask.Pos targets j then a else 0) = 22 * a := by
    intro a
    rw [sum_range_table targets targets_injective 1869 targets_lt]
    · rw [Finset.sum_congr rfl (fun i _ => if_pos (show LowMask.Pos targets (targets i) from ⟨i, rfl⟩))]
      simp
    · intro j _ hp; rw [if_neg (fun ⟨i, hi⟩ => hp i hi)]
  have h3 : ∑ j ∈ Finset.range 1869, (ArithmeticBinaryPopulation.population
      (if LowMask.Pos targets j then Exp.exp v - 2 else 0) +
      (if LowMask.Pos targets j then 1 else 0)) = 22 * v := by
    rw [Finset.sum_congr rfl (fun j _ => key j), hk]
  rw [Finset.sum_add_distrib, hk, mul_one] at h3
  exact h3

/-- **The contract.** For `b = 2ᵏ` and `g < 4t`, the binomial calibration holds iff `g`
packs digits `z < b` whose successors are a zero of the gapN86 rows. -/
theorem contract (k g R N t : V) (hgt : g < 4 * t)
    (hR : ι R = Rq pR (ι (Exp.exp k)) (ι g)) (hN : ι N = Nq (ι (Exp.exp k)))
    (ht : ι t = tq (ι (Exp.exp k))) :
    N * N ∣ ArithmeticBinomPascal.binom (2 * R) R ↔
      ∃ z : Fin 31 → V, (∀ i, z i < Exp.exp k) ∧ g = ∑ i, z i * Bm (Exp.exp k) ^ weights i ∧
        ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  obtain ⟨hH8, hc⟩ := port_facts (V := V)
  have hb1 := one_le_ι (exp_pos k)
  obtain ⟨hGpos, -, -, -, -, -, -, -, -, -⟩ := prefix_pos (Exp.exp k) g (exp_pos k)
  obtain ⟨v, hv⟩ : ∃ v : V, v = 2134939 + k + k := ⟨_, rfl⟩
  obtain ⟨hkv, hv1, hBm⟩ := v_facts k v hv
  have hBv : ι (Exp.exp v) = Bq (ι (Exp.exp k)) := by rw [← hBm, ι_Bm]
  have hB2 : 2 ≤ Bm (Exp.exp k) := by
    apply ι_le_ι.mp
    rw [map_ofNat, ι_Bm]
    obtain ⟨hB32, -⟩ := scale_facts (ι (Exp.exp k)) Hc hb1 hH8 (hBb _)
    linarith
  -- the soundness-range bounds
  have hgt' : ι g < 4 * tq (ι (Exp.exp k)) := by
    rw [← ht, ← map_ofNat ι 4, ← map_mul]; exact ι_lt_ι.2 hgt
  obtain ⟨hSTL, hgN, hmN⟩ := sum_lt_L pR (ι (Exp.exp k)) (ι g) Hc hb1 hH8 (hBb _) hc
    (ι_nonneg g) hgt'
  -- `G*` as a model natural
  obtain ⟨G, hG⟩ := nonneg_iff.mp hGpos.le
  -- the blocks
  obtain ⟨K117, hK117d⟩ : ∃ K : V, K = 117 * v := ⟨_, rfl⟩
  have hK117 : Exp.exp K117 = Exp.exp v ^ 117 := by rw [hK117d, exp_mul_lit]
  have hιK : ι (Exp.exp K117) = N0 (ι (Exp.exp k)) := by rw [hK117, map_pow, hBv, N0]
  obtain ⟨X, hXd⟩ : ∃ X : V, X = TstN (Exp.exp v) + 2 * G := ⟨_, rfl⟩
  obtain ⟨Sc, hScd⟩ : ∃ S : V, S = g + X * Exp.exp K117 := ⟨_, rfl⟩
  obtain ⟨Tc, hTcd⟩ : ∃ T : V,
      T = lowMask (Exp.exp k) (Exp.exp v) + highMask (Exp.exp v) * Exp.exp K117 := ⟨_, rfl⟩
  have hlowι : ι (lowMask (Exp.exp k) (Exp.exp v)) = maskq (ι (Exp.exp k)) := by
    have h := congrArg ι (lowMask_dsum k v hkv)
    simp only [map_add, map_mul, map_one, map_sum, map_pow, P72Root.ι_tsub (one_le_exp k),
      hBv] at h
    rw [maskq, N0, ell]
    linear_combination h
  have hX : ι X = Tst (ι (Exp.exp k)) + 2 * Gs pR (ι (Exp.exp k)) (ι g) := by
    rw [hXd, map_add, map_mul, map_ofNat, ← hBm, ι_TstN, ← hG]
  have hSc : ι Sc = Scq pR (ι (Exp.exp k)) (ι g) := by
    rw [hScd, map_add, map_mul, hX, hιK, Scq]; ring
  have hTc : ι Tc = Tcq (ι (Exp.exp k)) := by
    rw [hTcd, map_add, map_mul, hlowι, hιK, ← hBm, ι_highMask _ hB2, Tcq]; ring
  -- the calibration
  obtain ⟨u, hud⟩ : ∃ u : V, u = 1 + k + 1986 * v := ⟨_, rfl⟩
  have hu : ι (Exp.exp u) = Lq (ι (Exp.exp k)) := by
    rw [hud, exp_add, exp_add, exp_one', exp_mul_lit, map_mul, map_mul, map_ofNat, map_pow, hBv,
      Lq]
  obtain ⟨ν, hνd⟩ : ∃ ν : V, ν = 16012032 + 1055 * v := ⟨_, rfl⟩
  have hNν : N = Exp.exp ν := by
    apply ι_injective
    rw [hN, Nq, thresholdScale_eq, hνd, exp_add, exp_mul_lit, map_mul, map_pow, hBv]
  have hST : Sc + Tc < Exp.exp u := by
    apply ι_lt_ι.mp; rw [map_add, hSc, hTc, hu]; exact hSTL
  have hRe : R + Sc + 1 = Exp.exp u * (Sc + Tc + 1) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [hR, hSc, hTc, hu, Rq]; ring
  have hlowlt : lowMask (Exp.exp k) (Exp.exp v) < Exp.exp K117 := by
    apply ι_lt_ι.mp; rw [hlowι, hιK]; exact hmN
  have hpopT : ArithmeticBinaryPopulation.population Tc =
      ArithmeticBinaryPopulation.population (highMask (Exp.exp v)) +
        ArithmeticBinaryPopulation.population (lowMask (Exp.exp k) (Exp.exp v)) := by
    rw [hTcd, add_comm, ArithmeticBinaryPopulation.concatenate _ _ _ hlowlt]
  have hν : 2 * ν = u + ArithmeticBinaryPopulation.population Tc := by
    have h1' := congrArg ι (pop_low k v hkv)
    have h2' := congrArg ι (pop_high v hv1)
    have hvι := congrArg ι hv
    rw [hpopT, hνd, hud]
    apply ι_injective
    simp only [map_add, map_mul, map_ofNat, map_one] at h1' h2' hvι ⊢
    linear_combination -h2' - h1' - 15 * hvι
  have hcal := SparseCentral.noCarry_iff_sq_dvd_sparse hST hRe hν
  have hNN : N * N = Exp.exp ν ^ 2 := by rw [hNν, pow_two]
  rw [hNN, ← hcal]
  -- concatenation
  have hgK : g < Exp.exp K117 := by apply ι_lt_ι.mp; rw [hιK]; exact hgN
  rw [hScd, hTcd, ← noCarry_concat hgK hlowlt]
  have hg117 : g < Exp.exp v ^ 117 := by rw [← hK117]; exact hgK
  rw [lowMask, LowMask.noCarry_code_iff_weights hkv weights weights_injective 117 weights_lt g hg117,
    hBm, hXd]
  constructor
  · rintro ⟨⟨z, hz, hgz⟩, hhigh⟩
    refine ⟨z, hz, hgz, ?_⟩
    have hGz : ι G = Gs pR (ι (Exp.exp k)) (ι (∑ i, z i * Bm (Exp.exp k) ^ weights i)) := by
      rw [hBm, ← hgz]; exact hG.symm
    have h := (high_iff k z hz G hGz).mp
    rw [hBm] at h
    exact h hhigh
  · rintro ⟨z, hz, hgz, hrows⟩
    refine ⟨⟨z, hz, hgz⟩, ?_⟩
    have hGz : ι G = Gs pR (ι (Exp.exp k)) (ι (∑ i, z i * Bm (Exp.exp k) ^ weights i)) := by
      rw [hBm, ← hgz]; exact hG.symm
    have h := (high_iff k z hz G hGz).mpr hrows
    rw [hBm] at h
    exact h

/-! ## From the parent source to the packed code -/

/-- A positive parent zero gives a binary `b = 2ᵏ` and a packed digit vector `z < b` with
`0 < g = Σ zᵢ B^{wᵢ} < bB¹¹⁶`, whose successors are a zero of the gapN86 rows. -/
theorem code_of_source (x : Fin 31 → V) (hx : ∀ i, 0 < x i)
    (hz : ∀ r, Source31Rows.rows pR (fun i => ι (x i)) r = 0) :
    ∃ k : V, ∃ z : Fin 31 → V, (∀ i, z i < Exp.exp k) ∧
      0 < ∑ i, z i * Bm (Exp.exp k) ^ weights i ∧
      ∑ i, z i * Bm (Exp.exp k) ^ weights i < Exp.exp k * Bm (Exp.exp k) ^ 116 ∧
      ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  -- the layout-free part: digits `z < 2ᵏ` from 101's construction
  obtain ⟨k, z, hzk, -, -, hrz⟩ := N101Contract.code_of_source x hx hz
  set B := Bm (Exp.exp k) with hBdef
  have hbB : Exp.exp k ≤ B := by
    rw [hBdef, Bm]
    have h1 : Exp.exp k ≤ Exp.exp k * Exp.exp k := le_mul_of_one_le_left (Arithmetic.zero_le _)
      (one_le_exp k)
    exact le_trans h1 (le_mul_of_one_le_left (Arithmetic.zero_le _) (one_le_exp _))
  have hB0 : 0 < B := lt_of_lt_of_le (exp_pos k) hbB
  refine ⟨k, z, hzk, ?_, ?_, hrz⟩
  · -- positivity: the all-one tuple is not a zero
    by_contra hcon
    have h0 : ∀ i, z i = 0 := by
      intro i
      have hle : z i * B ^ weights i ≤ ∑ j, z j * B ^ weights j :=
        Finset.single_le_sum (f := fun j => z j * B ^ weights j)
          (fun j _ => Arithmetic.zero_le _) (Finset.mem_univ i)
      have hs : ∑ j, z j * B ^ weights j = 0 := by
        rcases eq_or_lt_of_le (Arithmetic.zero_le (∑ j, z j * B ^ weights j)) with h | h
        · exact h.symm
        · exact absurd h hcon
      rw [hs] at hle
      have hp : 0 < B ^ weights i := pow_pos hB0 _
      rcases eq_or_lt_of_le (Arithmetic.zero_le (z i)) with h | h
      · exact h.symm
      · exact absurd (lt_of_lt_of_le (mul_pos h hp) hle) (_root_.lt_irrefl _)
    have h4 := hrz 4
    have e : (fun i => ι (z i + 1)) = fun _ => (1 : DiffRing V) := by
      funext i; rw [h0 i, zero_add, map_one]
    rw [e] at h4
    have e4 : N101Source.rows pR (fun _ => (1 : DiffRing V)) 4 =
        ((-1)) * (1 * 1) + ((1)) * 1 + ((1)) * (1 * 1) := rfl
    rw [e4] at h4
    norm_num at h4
  · -- the cap `g < b B¹¹⁶`
    let f : ℕ → V := fun j => if h : LowMask.Pos weights j then z (Classical.choose h) else 0
    have hfw : ∀ i, f (weights i) = z i := by
      intro i
      have h : LowMask.Pos weights (weights i) := ⟨i, rfl⟩
      simp only [f, dif_pos h]
      congr 1
      exact weights_injective (Classical.choose_spec h)
    have hsum : ∑ i, z i * B ^ weights i = dsum B f (116 + 1) := by
      rw [LowMask.dsum_weights B weights weights_injective (116 + 1) weights_lt f
        (fun j _ hp => by simp only [f, dif_neg hp])]
      exact Finset.sum_congr rfl (fun i _ => by rw [hfw])
    rw [hsum]
    apply dsum_lt_mul hbB
    intro j _
    by_cases hp : LowMask.Pos weights j
    · simp only [f, dif_pos hp]; exact hzk _
    · simp only [f, dif_neg hp]; exact exp_pos k

end Nine121.N105Contract

#print axioms Nine121.N105Contract.prefix_naturals
#print axioms Nine121.N105Contract.contract
#print axioms Nine121.N105Contract.code_of_source
