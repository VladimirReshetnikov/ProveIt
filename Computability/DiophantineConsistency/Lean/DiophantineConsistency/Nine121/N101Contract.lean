import DiophantineConsistency.Nine121.N101Prefix
import DiophantineConsistency.Nine121.N101Source
import DiophantineConsistency.Nine121.Source31Facts
import DiophantineConsistency.Nine121.LowMask
import DiophantineConsistency.Nine121.SignedDigits
import DiophantineConsistency.Nine121.DigitPopulation
import DiophantineConsistency.Nine121.SparseCentral
import DiophantineConsistency.Mixed121.Mixed121Cell

/-! # Package 101's 420 prefix contract in every model of `𝗜𝚺₁`

At the wang943-mixed-121x8801 ports `pR = portsR Mixed121Ports.ports`:

* `prefix_naturals`: for every model natural `b > 0` and `g`, the prefix registers `R, N, t`
  of `N101Prefix` are images of model naturals with `R, N ≥ 8`, `b ≤ R, N`, `t > 0` (this is
  where the unconditional positivity of `G*` is used);
* `contract`: for `b = 2ᵏ` and `g < 4t`,
  `N² ∣ C(2R, R) ↔ ∃ z, (∀ i, zᵢ < b) ∧ g = Σᵢ zᵢ B^{wᵢ} ∧ ∀ r, ρ_r(z + 1) = 0`, with `ρ` the
  gapN86 rows (`N101Source.rows`). The proof is the sparse calibration
  (`SparseCentral`, population `σ(T_c) = 138v − 31k − 22`), the concatenation at `N₀ = B¹¹⁶`,
  the low mask (`LowMask`) and the high block (`SignedDigits.high_noCarry_iff` with
  `N101Layout.coeff_target` and the coefficient bound of `N101Prefix`);
* `code_of_source`: a positive parent zero gives `k`, a digit vector `z` with `zᵢ < 2ᵏ`, a
  positive `g = Σ zᵢ B^{wᵢ} < bB¹¹⁵` and vanishing gapN86 rows at `z + 1`;
* `source_of_code`: vanishing gapN86 rows at `z + 1` give a positive parent zero.

The coefficient bound `H = 2^2134927` follows from `β < 2^1064921`, `K < 2^1070004`
(`Mixed121Cell.symbolic_kernel_lt`), `MC < β` and `MF < 2β`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N101Contract
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelDigitTransfer ModelCarries ArithmeticBinaryCarry
open N101Layout N101Prefix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl

theorem port1_lt : ((Mixed121Ports.ports 1 : ℕ) : V) < Exp.exp (1070004 : V) := by
  unfold Mixed121Ports.ports
  rw [ports_one]
  exact Mixed121Cell.symbolic_kernel_lt

theorem port0_lt : ((Mixed121Ports.ports 0 : ℕ) : V) < Exp.exp (1064921 : V) := by
  rw [Mixed121Ports.port_beta, show (121 : V) * 8801 = 1064921 by norm_num]
  exact tsub_lt_self (exp_pos _) one_pos

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-! ## Scales -/

theorem ι_exp_nat (n : ℕ) : ι (Exp.exp (n : V)) = (2 : DiffRing V) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, exp_succ, map_mul, ih, map_ofNat]; ring

theorem exp_one' : Exp.exp (1 : V) = 2 := by
  have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this

theorem exp_two' : Exp.exp (2 : V) = 4 := by
  have := exp_succ (1 : V); rw [one_add_one_eq_two, exp_one'] at this; rw [this]; norm_num

theorem exp_pow_nat (v : V) (n : ℕ) : Exp.exp v ^ n = Exp.exp ((n : V) * v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, exp_add]

/-- The coefficient bound `H = 2^2134927`. -/
def Hc : DiffRing V := ι (Exp.exp (2134927 : V))

theorem baseScale_eq' : ((baseScale : ℤ) : DiffRing V) = ι (Exp.exp (2134939 : V)) := by
  have h := ι_exp_nat (V := V) 2134939
  rw [Nat.cast_ofNat] at h
  rw [h, baseScale, Int.cast_pow, Int.cast_ofNat]

theorem ι_exp_twelve : ι (Exp.exp (12 : V)) = 4096 := by
  have h := ι_exp_nat (V := V) 12
  rw [Nat.cast_ofNat] at h
  rw [h]; norm_num

theorem baseScale_eq : ((baseScale : ℤ) : DiffRing V) = 4096 * Hc := by
  rw [baseScale_eq', Hc, show (2134939 : V) = 12 + 2134927 by norm_num, exp_add, map_mul,
    ι_exp_twelve]

theorem thresholdScale_eq : ((thresholdScale : ℤ) : DiffRing V) = ι (Exp.exp (16012032 : V)) := by
  have h := ι_exp_nat (V := V) 16012032
  rw [Nat.cast_ofNat] at h
  rw [h, thresholdScale, Int.cast_pow, Int.cast_ofNat]

/-- The model-natural base `B = 2^2134939 b²`. -/
def Bm (b : V) : V := Exp.exp (2134939 : V) * (b * b)

theorem ι_Bm (b : V) : ι (Bm b) = Bq (ι b) := by
  rw [Bm, map_mul, map_mul, Bq, baseScale_eq']

theorem hBb (b : V) : 4096 * Hc * (ι b * ι b) ≤ Bq (ι b) :=
  le_of_eq (by rw [Bq, baseScale_eq])

theorem exp_ge_eight {n : V} (hn : 3 ≤ n) : (8 : DiffRing V) ≤ ι (Exp.exp n) := by
  have h := ι_exp_nat (V := V) 3
  rw [Nat.cast_ofNat] at h
  have h3 : ι (Exp.exp (3 : V)) ≤ ι (Exp.exp n) := ι_le_ι.2 (exp_monotone_le.2 hn)
  rw [h] at h3
  linarith [show (2 : DiffRing V) ^ 3 = 8 by norm_num]

/-! ## Port bounds -/

theorem port_arith (a0 a1 E1 E2 H : DiffRing V) (hp0 : 0 ≤ a0) (hp1 : 0 ≤ a1) (e0 : a0 ≤ E1)
    (e1 : a1 + 1 ≤ E2) (h8 : 8 ≤ E1) (h2E : 2 * E1 ≤ E2) (hE : H = 4 * E1 * E2) :
    8 ≤ H ∧ 6 * a0 ≤ H ∧ 6 * a0 ^ 2 ≤ H ∧ 2 * a1 + 2 ≤ H ∧ 2 * a0 + 2 * a0 * a1 ≤ H := by
  subst hE
  have hE1 : 0 ≤ E1 := by linarith
  have hE2 : 16 ≤ E2 := by linarith
  have m1 : 8 * E2 ≤ E1 * E2 := mul_le_mul_of_nonneg_right h8 (by linarith)
  have m2 : E1 * 16 ≤ E1 * E2 := mul_le_mul_of_nonneg_left hE2 hE1
  have m3 : a0 * a0 ≤ E1 * E1 := mul_le_mul e0 e0 hp0 hE1
  have m4 : E1 * (2 * E1) ≤ E1 * E2 := mul_le_mul_of_nonneg_left h2E hE1
  have m5 : a0 * (a1 + 1) ≤ E1 * E2 := mul_le_mul e0 e1 (by linarith) hE1
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem Hc_eq : (Hc : DiffRing V) = 4 * ι (Exp.exp (1064921 : V)) * ι (Exp.exp (1070004 : V)) := by
  rw [Hc, show (2134927 : V) = 2 + 1064921 + 1070004 by norm_num, exp_add, exp_add, map_mul,
    map_mul, exp_two', map_ofNat]

theorem port_facts :
    (8 : DiffRing V) ≤ Hc ∧
      ((∀ q, |c0 pR q| ≤ Hc) ∧ (∀ q, |c1 pR q| ≤ Hc) ∧ (∀ q, |c2 pR q| ≤ Hc)) := by
  obtain ⟨_, hl, hh, _⟩ := Mixed121Ports.leaf_bounds (V := V)
  have h0 := port0_lt (V := V)
  have h1 := port1_lt (V := V)
  have e0 : ι ((Mixed121Ports.ports 0 : ℕ) : V) ≤ ι (Exp.exp (1064921 : V)) := ι_le_ι.2 h0.le
  have e1 : ι ((Mixed121Ports.ports 1 : ℕ) : V) + 1 ≤ ι (Exp.exp (1070004 : V)) := by
    have := ι_le_ι.2 (lt_iff_succ_le.mp h1); rwa [map_add, map_one] at this
  have h8 : (8 : DiffRing V) ≤ ι (Exp.exp (1064921 : V)) := exp_ge_eight (by norm_num)
  have h2E : 2 * ι (Exp.exp (1064921 : V)) ≤ ι (Exp.exp (1070004 : V)) := by
    have : Exp.exp ((1064921 : V) + 1) ≤ Exp.exp (1070004 : V) := exp_monotone_le.2 (by norm_num)
    rw [exp_succ] at this
    have := ι_le_ι.2 this
    rwa [map_mul, map_ofNat] at this
  obtain ⟨hH8, hβ, hββ, hK, hβK⟩ := port_arith _ _ _ _ _ (ι_nonneg _) (ι_nonneg _) e0 e1 h8 h2E
    (Hc_eq (V := V))
  refine ⟨hH8, ?_⟩
  rw [Source31Facts.portsR_eq]
  have h20 : ι ((Mixed121Ports.ports 2 : ℕ) : V) ≤ ι ((Mixed121Ports.ports 0 : ℕ) : V) :=
    ι_le_ι.2 hl.le
  have h30 : ι ((Mixed121Ports.ports 3 : ℕ) : V) ≤ 2 * ι ((Mixed121Ports.ports 0 : ℕ) : V) := by
    have := ι_le_ι.2 hh.le; rwa [map_mul, map_ofNat] at this
  exact c_bounds (fun j => ι ((Mixed121Ports.ports j : ℕ) : V)) Hc (ι_nonneg _) (ι_nonneg _)
    (ι_nonneg _) (ι_nonneg _) h20 h30 hH8 hβ hββ hK hβK

/-! ## The prefix registers are model naturals -/

theorem one_le_ι {b : V} (hb : 0 < b) : (1 : DiffRing V) ≤ ι b := by
  have := ι_le_ι.2 (pos_iff_one_le.mp hb); rwa [map_one] at this

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
    have a1 : ell (ι b) * (ι b - 1) ≤ 31 * Bq (ι b) ^ 115 * ι b :=
      mul_le_mul hl (by linarith) (by linarith) (by linarith [hP 115])
    have a2 : 4096 * (ι b * ι b) * Bq (ι b) ^ 115 ≤ Bq (ι b) * Bq (ι b) ^ 115 :=
      mul_le_mul_of_nonneg_right hBb4 (hP 115)
    have a3 : 31 * Bq (ι b) ^ 115 * ι b ≤ 31 * (ι b * ι b) * Bq (ι b) ^ 115 := by
      have := mul_le_mul_of_nonneg_right hbb (hP 115); linarith
    have a4 : (1 : DiffRing V) ≤ (ι b * ι b) * Bq (ι b) ^ 115 :=
      le_trans (le_trans hb1 hbb) (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
    linarith
  have hTc : 0 ≤ Tcq (ι b) := by
    rw [Tcq]
    have := mul_nonneg (pow_nonneg hB0 116) (mul_nonneg hT0 (by linarith : (0 : DiffRing V) ≤ Bq (ι b) - 2))
    unfold N0; linarith
  have hSc : 0 ≤ Scq pR (ι b) (ι g) := by
    rw [Scq]
    have := mul_nonneg (pow_nonneg hB0 116) (by linarith : (0 : DiffRing V) ≤ Tst (ι b) + 2 * Gs pR (ι b) (ι g))
    unfold N0; linarith
  have hLb : Bq (ι b) ≤ Bq (ι b) ^ 1983 := by
    have := pow_step _ hB1 1 1983 (by norm_num); rwa [pow_one] at this
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
  have hB1053 : Bq (ι b) ≤ Bq (ι b) ^ 1053 := by
    have := pow_step _ hB1 1 1053 (by norm_num); rwa [pow_one] at this
  have hN : 8 * Bq (ι b) ≤ Nq (ι b) := by
    rw [Nq, thresholdScale_eq]
    exact mul_le_mul hN8 hB1053 hB0 (by linarith)
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
def highMask (B : V) : V := dsum B (fun e => if LowMask.Pos targets e then B - 2 else 0) 1867

/-- The low code mask. -/
def lowMask (b B : V) : V := dsum B (codeMask b B (LowMask.Pos weights)) 116

theorem ι_TstN (b : V) : ι (TstN (Bm b)) = Tst (ι b) := by
  simp only [TstN, map_sum, map_pow, ι_Bm, Tst]

theorem targets_lt : ∀ r, targets r < 1867 := fun r => lt_of_le_of_lt (targets_le r) (by norm_num)
theorem weights_lt : ∀ i, weights i < 116 := fun i => lt_of_le_of_lt (weights_le i) (by norm_num)

theorem highMask_eq (B : V) : highMask B = ∑ r, (B - 2) * B ^ targets r := by
  rw [highMask, LowMask.dsum_weights B targets targets_injective 1867 targets_lt]
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
      Exp.exp v ^ 116 := by
  have h := codeMask_dsum (one_le_exp k) (exp_monotone_le.2 hkv) (LowMask.Pos weights) 116
  have hd : dsum (Exp.exp v) (codeInd (LowMask.Pos weights)) 116 = ∑ i, Exp.exp v ^ weights i := by
    rw [LowMask.dsum_weights _ weights weights_injective 116 weights_lt]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [codeInd, if_pos ⟨i, rfl⟩, one_mul]
    · intro j _ hp; rw [codeInd, if_neg hp]
  rw [← hd]; exact h

theorem exp_mul_lit (v : V) (n : ℕ) [n.AtLeastTwo] :
    Exp.exp ((OfNat.ofNat n : V) * v) = Exp.exp v ^ (OfNat.ofNat n : ℕ) := by
  have h := exp_pow_nat v (OfNat.ofNat n)
  rw [Nat.cast_ofNat] at h
  exact h.symm

theorem v_facts (k v : V) (hv : v = 2134939 + k + k) :
    k ≤ v ∧ 1 ≤ v ∧ Bm (Exp.exp k) = Exp.exp v := by
  refine ⟨by rw [hv]; exact le_add_left le_rfl, ?_, ?_⟩
  · rw [hv]; exact le_trans (by norm_num) (le_add_right (le_add_right le_rfl))
  · rw [Bm, hv, exp_add, exp_add, mul_assoc]

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
  have hcb : ∀ e < 1867,
      4 * |(sourcePoly pR (fun i => ι (z i + 1))).coeff e| + 4 ≤ ι (Exp.exp v) := by
    intro e _
    rw [hBv]
    refine coeff_bound pR _ Hc hb1 hH8 (hBb _) hc _ (fun i => ι_nonneg _) (fun i => ?_) e
    exact ι_le_ι.2 (lt_iff_succ_le.mp (hz i))
  have hT : Tst (ι (Exp.exp k)) = ∑ e ∈ Finset.range 1867,
      (if LowMask.Pos targets e then (1 : DiffRing V) else 0) * Bq (ι (Exp.exp k)) ^ e := by
    rw [Tst, sum_range_table targets targets_injective 1867 targets_lt]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [if_pos ⟨r, rfl⟩, one_mul]
    · intro j _ hp
      rw [if_neg (fun ⟨r, hr⟩ => hp r hr), zero_mul]
  have hX : ι (TstN (Bm (Exp.exp k)) + 2 * G) =
      ∑ e ∈ Finset.range 1867,
        (2 * (sourcePoly pR (fun i => ι (z i + 1))).coeff e +
          if LowMask.Pos targets e then 1 else 0) * ι (Exp.exp v) ^ e := by
    rw [map_add, map_mul, map_ofNat, ι_TstN, hG, Gs_sum pR _ _ _ hu, hBv, hT, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have key := SignedDigits.high_noCarry_iff v hv1 1867 (LowMask.Pos targets)
    (fun e => (sourcePoly pR (fun i => ι (z i + 1))).coeff e) hcb _ hX
  have hmask : highMask (Bm (Exp.exp k)) =
      dsum (Exp.exp v) (fun e => if LowMask.Pos targets e then Exp.exp v - 2 else 0) 1867 := by
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
    ArithmeticBinaryPopulation.population (lowMask (Exp.exp k) (Exp.exp v)) + 31 * k = 116 * v := by
  have hdig : ∀ j < 116, codeMask (Exp.exp k) (Exp.exp v) (LowMask.Pos weights) j < Exp.exp v := by
    intro j _
    unfold codeMask
    split_ifs
    · exact tsub_lt_self (exp_pos v) (exp_pos k)
    · exact tsub_lt_self (exp_pos v) one_pos
  rw [lowMask, DigitPopulation.population_dsum v _ 116 hdig]
  have key : ∀ j, ArithmeticBinaryPopulation.population
      (codeMask (Exp.exp k) (Exp.exp v) (LowMask.Pos weights) j) +
      (if LowMask.Pos weights j then k else 0) = v := by
    intro j
    unfold codeMask
    split_ifs
    · rw [DigitPopulation.population_exp_sub_exp hkv, tsub_add_cancel_of_le hkv]
    · rw [ArithmeticBinaryPopulation.population_exp_sub_one, add_zero]
  have hk : ∑ j ∈ Finset.range 116, (if LowMask.Pos weights j then k else 0) = 31 * k := by
    rw [sum_range_table weights weights_injective 116 weights_lt]
    · rw [Finset.sum_congr rfl (fun i _ => if_pos (show LowMask.Pos weights (weights i) from ⟨i, rfl⟩))]
      simp
    · intro j _ hp; rw [if_neg (fun ⟨i, hi⟩ => hp i hi)]
  have h3 : ∑ j ∈ Finset.range 116, (ArithmeticBinaryPopulation.population
      (codeMask (Exp.exp k) (Exp.exp v) (LowMask.Pos weights) j) +
      (if LowMask.Pos weights j then k else 0)) = 116 * v := by
    rw [Finset.sum_congr rfl (fun j _ => key j)]; simp
  rw [Finset.sum_add_distrib, hk] at h3
  exact h3

theorem pop_high (v : V) (hv : 1 ≤ v) :
    ArithmeticBinaryPopulation.population (highMask (Exp.exp v)) + 22 = 22 * v := by
  have hdig : ∀ j < 1867, (fun e => if LowMask.Pos targets e then Exp.exp v - 2 else 0) j <
      Exp.exp v := by
    intro j _
    dsimp only
    split_ifs
    · exact tsub_lt_self (exp_pos v) (by norm_num)
    · exact exp_pos v
  rw [highMask, DigitPopulation.population_dsum v _ 1867 hdig]
  have h2 : Exp.exp v - 2 = Exp.exp v - Exp.exp 1 := by rw [exp_one']
  have key : ∀ j, ArithmeticBinaryPopulation.population
      (if LowMask.Pos targets j then Exp.exp v - 2 else 0) +
      (if LowMask.Pos targets j then 1 else 0) = if LowMask.Pos targets j then v else 0 := by
    intro j
    split_ifs
    · rw [h2, DigitPopulation.population_exp_sub_exp hv, tsub_add_cancel_of_le hv]
    · rw [DigitPopulation.population_zero, add_zero]
  have hk : ∀ a : V, ∑ j ∈ Finset.range 1867, (if LowMask.Pos targets j then a else 0) = 22 * a := by
    intro a
    rw [sum_range_table targets targets_injective 1867 targets_lt]
    · rw [Finset.sum_congr rfl (fun i _ => if_pos (show LowMask.Pos targets (targets i) from ⟨i, rfl⟩))]
      simp
    · intro j _ hp; rw [if_neg (fun ⟨i, hi⟩ => hp i hi)]
  have h3 : ∑ j ∈ Finset.range 1867, (ArithmeticBinaryPopulation.population
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
  obtain ⟨K116, hK116d⟩ : ∃ K : V, K = 116 * v := ⟨_, rfl⟩
  have hK116 : Exp.exp K116 = Exp.exp v ^ 116 := by rw [hK116d, exp_mul_lit]
  have hιK : ι (Exp.exp K116) = N0 (ι (Exp.exp k)) := by rw [hK116, map_pow, hBv, N0]
  obtain ⟨X, hXd⟩ : ∃ X : V, X = TstN (Exp.exp v) + 2 * G := ⟨_, rfl⟩
  obtain ⟨Sc, hScd⟩ : ∃ S : V, S = g + X * Exp.exp K116 := ⟨_, rfl⟩
  obtain ⟨Tc, hTcd⟩ : ∃ T : V,
      T = lowMask (Exp.exp k) (Exp.exp v) + highMask (Exp.exp v) * Exp.exp K116 := ⟨_, rfl⟩
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
  obtain ⟨u, hud⟩ : ∃ u : V, u = 1 + k + 1983 * v := ⟨_, rfl⟩
  have hu : ι (Exp.exp u) = Lq (ι (Exp.exp k)) := by
    rw [hud, exp_add, exp_add, exp_one', exp_mul_lit, map_mul, map_mul, map_ofNat, map_pow, hBv,
      Lq]
  obtain ⟨ν, hνd⟩ : ∃ ν : V, ν = 16012032 + 1053 * v := ⟨_, rfl⟩
  have hNν : N = Exp.exp ν := by
    apply ι_injective
    rw [hN, Nq, thresholdScale_eq, hνd, exp_add, exp_mul_lit, map_mul, map_pow, hBv]
  have hST : Sc + Tc < Exp.exp u := by
    apply ι_lt_ι.mp; rw [map_add, hSc, hTc, hu]; exact hSTL
  have hRe : R + Sc + 1 = Exp.exp u * (Sc + Tc + 1) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [hR, hSc, hTc, hu, Rq]; ring
  have hlowlt : lowMask (Exp.exp k) (Exp.exp v) < Exp.exp K116 := by
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
  have hgK : g < Exp.exp K116 := by apply ι_lt_ι.mp; rw [hιK]; exact hgN
  rw [hScd, hTcd, ← noCarry_concat hgK hlowlt]
  have hg116 : g < Exp.exp v ^ 116 := by rw [← hK116]; exact hgK
  rw [lowMask, LowMask.noCarry_code_iff_weights hkv weights weights_injective 116 weights_lt g hg116,
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

/-! ## Between the parent source and the packed code -/

/-- Vanishing gapN86 rows at `z + 1` give a positive parent zero. -/
theorem source_of_code (z : Fin 31 → V) (h : ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0) :
    ∃ x : Fin 31 → V, (∀ i, 0 < x i) ∧ ∀ r, Source31Rows.rows pR (fun i => ι (x i)) r = 0 := by
  refine ⟨fun i => if i = 18 then (z 18 + 1) + (z 12 + 1) + (z 13 + 1) else
    if i = 16 then (z 16 + 1) + 1 else z i + 1, fun i => ?_, fun r => ?_⟩
  · dsimp only
    split_ifs <;> first
      | exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) one_pos
      | exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _)
          (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) one_pos)
  · have e : N101Source.toOld (fun i => ι (z i + 1)) = fun i => ι (if i = 18 then
        (z 18 + 1) + (z 12 + 1) + (z 13 + 1) else if i = 16 then (z 16 + 1) + 1 else z i + 1) := by
      funext i
      simp only [N101Source.toOld]
      split_ifs <;> simp only [map_add, map_one]
    rw [← e]
    exact (N101Source.zero_iff _ _).mp h r

/-- A positive parent zero gives a binary `b = 2ᵏ` and a packed digit vector `z < b` with
`0 < g = Σ zᵢ B^{wᵢ} < bB¹¹⁵`, whose successors are a zero of the gapN86 rows. -/
theorem code_of_source (x : Fin 31 → V) (hx : ∀ i, 0 < x i)
    (hz : ∀ r, Source31Rows.rows pR (fun i => ι (x i)) r = 0) :
    ∃ k : V, ∃ z : Fin 31 → V, (∀ i, z i < Exp.exp k) ∧
      0 < ∑ i, z i * Bm (Exp.exp k) ^ weights i ∧
      ∑ i, z i * Bm (Exp.exp k) ^ weights i < Exp.exp k * Bm (Exp.exp k) ^ 115 ∧
      ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  have F := Source31Rows.facts pR (fun i => ι (x i)) hz
  dsimp only at F
  obtain ⟨-, h16, -, -, -, h19, -⟩ := F
  have r6 : ι (x 18) + (-1) * (ι (x 17) * ι (x 19)) + (-1) * ι (x 13) + (-1) * ι (x 12) +
      ι (x 12) * ι (x 17) = 0 := hz 6
  have hι1 : ∀ i, (1 : DiffRing V) ≤ ι (x i) := fun i => one_le_ι (hx i)
  have e18 : ι (x 18) - (ι (x 12) + ι (x 13)) =
      ι (x 17) * ((ι (x 9) * ι (x 16)) * (ι (x 12) + ι (x 13))) := by
    linear_combination r6 + ι (x 17) * h19
  have hpι : ∀ i, (0 : DiffRing V) < ι (x i) := fun i => lt_of_lt_of_le one_pos (hι1 i)
  have hp18 : 0 < ι (x 17) * ((ι (x 9) * ι (x 16)) * (ι (x 12) + ι (x 13))) :=
    mul_pos (hpι 17) (mul_pos (mul_pos (hpι 9) (hpι 16)) (add_pos (hpι 12) (hpι 13)))
  have h18 : x 12 + x 13 < x 18 := by
    apply ι_lt_ι.mp; rw [map_add]; linarith
  have hβ : (1 : DiffRing V) ≤ pR 0 := by
    rw [Source31Facts.portsR_eq]
    obtain ⟨hb0, -⟩ := Mixed121Ports.leaf_bounds (V := V)
    exact one_le_ι hb0
  have hq : (2 : DiffRing V) ≤ pR 0 * ι (x 0) + 1 := by
    have := hι1 0
    nlinarith
  have hq2 : (4 : DiffRing V) ≤ (pR 0 * ι (x 0) + 1) * (pR 0 * ι (x 0) + 1) := by nlinarith
  have hq3 : (8 : DiffRing V) ≤
      (pR 0 * ι (x 0) + 1) * ((pR 0 * ι (x 0) + 1) * (pR 0 * ι (x 0) + 1)) := by nlinarith
  have h16' : 1 < x 16 := by
    apply ι_lt_ι.mp
    rw [map_one, h16]
    linarith
  -- the gapN86 coordinates
  let y : Fin 31 → V := fun i => if i = 18 then x 18 - (x 12 + x 13) else
    if i = 16 then x 16 - 1 else x i
  have hy : ∀ i, 1 ≤ y i := by
    intro i
    simp only [y]
    split_ifs
    · exact pos_iff_one_le.mp (lt_tsub_iff_left.mpr (by simpa using h18))
    · exact pos_iff_one_le.mp (lt_tsub_iff_left.mpr (by simpa using h16'))
    · exact pos_iff_one_le.mp (hx i)
  have y18 : y 18 = x 18 - (x 12 + x 13) := rfl
  have y16 : y 16 = x 16 - 1 := rfl
  have y12 : y 12 = x 12 := rfl
  have y13 : y 13 = x 13 := rfl
  have hold : N101Source.toOld (fun i => ι (y i)) = fun i => ι (x i) := by
    funext i
    simp only [N101Source.toOld]
    by_cases h1 : i = 18
    · subst h1
      rw [if_pos rfl, y18, y12, y13, P72Root.ι_tsub h18.le, map_add]; ring
    · rw [if_neg h1]
      by_cases h2 : i = 16
      · subst h2
        rw [if_pos rfl, y16, P72Root.ι_tsub h16'.le, map_one]; ring
      · rw [if_neg h2]
        simp only [y, if_neg h1, if_neg h2]
  have hrows : ∀ r, N101Source.rows pR (fun i => ι (y i)) r = 0 := by
    intro r
    apply (N101Source.zero_iff _ _).mpr
    rw [hold]; exact hz
  -- the digits
  let zz : Fin 31 → V := fun i => y i - 1
  have hzz : ∀ i, zz i + 1 = y i := fun i => tsub_add_cancel_of_le (hy i)
  let k : V := ∑ i, y i
  have hzk : ∀ i, zz i < Exp.exp k := by
    intro i
    have a1 : zz i < y i := by rw [← hzz i]; exact lt_add_one _
    have a2 : y i ≤ k := Finset.single_le_sum (f := y) (fun j _ => Arithmetic.zero_le _)
      (Finset.mem_univ i)
    exact lt_of_lt_of_le a1 (le_trans a2 (lt_exp k).le)
  have hrz : ∀ r, N101Source.rows pR (fun i => ι (zz i + 1)) r = 0 := by
    intro r; simp only [hzz]; exact hrows r
  set B := Bm (Exp.exp k) with hBdef
  have hbB : Exp.exp k ≤ B := by
    rw [hBdef, Bm]
    have h1 : Exp.exp k ≤ Exp.exp k * Exp.exp k := le_mul_of_one_le_left (Arithmetic.zero_le _)
      (one_le_exp k)
    exact le_trans h1 (le_mul_of_one_le_left (Arithmetic.zero_le _) (one_le_exp _))
  have hB0 : 0 < B := lt_of_lt_of_le (exp_pos k) hbB
  refine ⟨k, zz, hzk, ?_, ?_, hrz⟩
  · -- positivity: the all-one tuple is not a zero
    by_contra hcon
    have h0 : ∀ i, zz i = 0 := by
      intro i
      have hle : zz i * B ^ weights i ≤ ∑ j, zz j * B ^ weights j :=
        Finset.single_le_sum (f := fun j => zz j * B ^ weights j)
          (fun j _ => Arithmetic.zero_le _) (Finset.mem_univ i)
      have hs : ∑ j, zz j * B ^ weights j = 0 := by
        rcases eq_or_lt_of_le (Arithmetic.zero_le (∑ j, zz j * B ^ weights j)) with h | h
        · exact h.symm
        · exact absurd h hcon
      rw [hs] at hle
      have hp : 0 < B ^ weights i := pow_pos hB0 _
      rcases eq_or_lt_of_le (Arithmetic.zero_le (zz i)) with h | h
      · exact h.symm
      · exact absurd (lt_of_lt_of_le (mul_pos h hp) hle) (_root_.lt_irrefl _)
    have h4 := hrz 4
    have e : (fun i => ι (zz i + 1)) = fun _ => (1 : DiffRing V) := by
      funext i; rw [h0 i, zero_add, map_one]
    rw [e] at h4
    have e4 : N101Source.rows pR (fun _ => (1 : DiffRing V)) 4 =
        ((-1)) * (1 * 1) + ((1)) * 1 + ((1)) * (1 * 1) := rfl
    rw [e4] at h4
    norm_num at h4
  · -- the cap `g < b B¹¹⁵`
    let f : ℕ → V := fun j => if h : LowMask.Pos weights j then zz (Classical.choose h) else 0
    have hfw : ∀ i, f (weights i) = zz i := by
      intro i
      have h : LowMask.Pos weights (weights i) := ⟨i, rfl⟩
      simp only [f, dif_pos h]
      congr 1
      exact weights_injective (Classical.choose_spec h)
    have hsum : ∑ i, zz i * B ^ weights i = dsum B f (115 + 1) := by
      rw [LowMask.dsum_weights B weights weights_injective (115 + 1) weights_lt f
        (fun j _ hp => by simp only [f, dif_neg hp])]
      exact Finset.sum_congr rfl (fun i _ => by rw [hfw])
    rw [hsum]
    apply dsum_lt_mul hbB
    intro j _
    by_cases hp : LowMask.Pos weights j
    · simp only [f, dif_pos hp]; exact hzk _
    · simp only [f, dif_neg hp]; exact exp_pos k

end Nine121.N101Contract

#print axioms Nine121.N101Contract.prefix_naturals
#print axioms Nine121.N101Contract.contract
#print axioms Nine121.N101Contract.source_of_code
#print axioms Nine121.N101Contract.code_of_source
