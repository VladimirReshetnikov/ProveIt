import DiophantineConsistency.Z10.Z10Prefix
import DiophantineConsistency.Z10.Z10SparseCentral
import DiophantineConsistency.Nine121.N105Contract

/-! # Ten-integer package 106: the central-binomial contract

Soundness step S16 and completeness step C4 of the route. At `b = 2ᵏ` the base is
`Bc b = 2ᵛ` with `v = 2134940 + 2k`, and the prefix registers of `Z10Regs` are

  `S = g + N0 · (AT + 2 · coded)`,   `T = (mask − 2) + N0 · AT · (Bc − 2)`,
  `X = NN · (S + T + 1) − S − 1`,    `Y = b · 2^34159017 · Bc^2109`,

with `N0 = Bc^117` and `NN = Bc^1986`. This is the sparse rank of packages 101/105 at the
plain power of two `Y = 2ᵐ`, `m = k + 34159017 + 2109 v`, and with a mask that is the mask of
package 105 minus two. `contract` states

  `Y ∣ binom (2X) X  ↔  g = ∑ zᵢ Bc^wᵢ` with all `zᵢ < b`, and the 22 rows of the source
  system vanish at `zᵢ + 1`,

for a low word `g < 4 · cap` that is divisible by four.

* The base-generic masks `TstN`, `highMask`, `lowMask` of `N105Contract` and their population
  counts are reused as they stand; `ι_TstN`, `ι_highMask` and `high_iff` are the statements
  of `N105Contract` at the base `Bcm`.
* The low mask is `4q + 3` (`lowMask_four_three`), so the low block of `T` is `4q + 1`.
  `Z10SparseCentral.population_low` accounts for the missing unit of population in the
  calibration `m = u + σ(T)`, and `Z10SparseCentral.noCarry_low` shows that the carry
  condition against `g = 4a` is unchanged.
* The calibration is the identity `m − (u + σ(T)) = −16 · (v − 2134940 − 2k)` with
  `u = 1986 v`, `σ(T) = (22v − 22) + (117v − 31k − 1)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Z10Contract
open Polynomial
open Nine121 Nine121.SparseExtraction Nine121.N105Layout Z10Regs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelDigitTransfer ModelCarries ArithmeticBinaryCarry
open ArithmeticBinaryPopulation ArithmeticBinomPascal
open Z10Prefix Z10SparseCentral
open Nine121.N105Contract (TstN highMask lowMask targets_lt weights_lt highMask_eq lowMask_dsum
  pop_low pop_high)
open Nine121.N101Contract (Hc port_facts one_le_ι exp_mul_lit exp_two' hBb baseScale_eq)
open Nine121.N101Prefix (Bq sum_range_table)
open Nine121.N105Prefix (coeff_bound)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

theorem weights_pos : ∀ i, 1 ≤ weights i := by decide +kernel

/-! ## The masks at the base `Bcm` -/

theorem ι_TstN (b : V) : ι (TstN (Bcm b)) = AT (ι b) := by
  simp only [TstN, map_sum, map_pow, ι_Bcm, AT]

theorem ι_highMask (b : V) (hB : 2 ≤ Bcm b) :
    ι (highMask (Bcm b)) = AT (ι b) * (Bc (ι b) - 2) := by
  rw [highMask_eq, map_sum, AT, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_mul, P72Root.ι_tsub hB, map_pow, ι_Bcm, map_ofNat]; ring

/-- The low mask is `≡ 3 (mod 4)`: every weight is positive and four divides the base. -/
theorem lowMask_four_three (k v : V) (hv : v = 2134940 + k + k) :
    ∃ q : V, lowMask (Exp.exp k) (Exp.exp v) = 4 * q + 3 := by
  have hkv : k ≤ v := by rw [hv]; exact le_add_left le_rfl
  have hv4 : (4 : V) ∣ Exp.exp v := by
    refine ⟨Exp.exp (2134938 + (k + k)), ?_⟩
    rw [hv, show (2134940 : V) = 2 + 2134938 by norm_num, add_assoc, add_assoc, exp_add,
      exp_two']
  have hw : ∀ i, (4 : V) ∣ Exp.exp v ^ weights i := fun i =>
    dvd_pow hv4 (Nat.one_le_iff_ne_zero.mp (weights_pos i))
  obtain ⟨c, hc⟩ : (4 : V) ∣ (Exp.exp k - 1) * ∑ i, Exp.exp v ^ weights i :=
    Dvd.dvd.mul_left (Finset.dvd_sum (fun i _ => hw i)) _
  obtain ⟨d, hd⟩ : (4 : V) ∣ Exp.exp v ^ 117 := dvd_pow hv4 (by norm_num)
  have h := lowMask_dsum k v hkv
  rw [hc, hd] at h
  exact four_three_of_eq h

/-! ## The high block: the rows of the source system -/

theorem high_iff (k : V) (z : Fin 31 → V) (hz : ∀ i, z i < Exp.exp k) (G : V)
    (hG : ι G = coded pR (ι (Exp.exp k)) (ι (∑ i, z i * Bcm (Exp.exp k) ^ weights i))) :
    NoCarry (TstN (Bcm (Exp.exp k)) + 2 * G) (highMask (Bcm (Exp.exp k))) ↔
      ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  obtain ⟨hH8, hc⟩ := port_facts (V := V)
  obtain ⟨v, hv⟩ : ∃ v : V, v = 2134940 + k + k := ⟨_, rfl⟩
  obtain ⟨-, hv1, hBm⟩ := v_facts k v hv
  have hb1 : (1 : DiffRing V) ≤ ι (Exp.exp k) := one_le_ι (exp_pos k)
  have hBv : ι (Exp.exp v) = Bc (ι (Exp.exp k)) := by rw [← hBm, ι_Bcm]
  have hu : word (ι (Exp.exp k)) (ι (∑ i, z i * Bcm (Exp.exp k) ^ weights i)) =
      ∑ i, (fun i => ι (z i + 1)) i * Bc (ι (Exp.exp k)) ^ weights i := by
    rw [word, ell, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, map_pow, ι_Bcm, map_add, map_one]; ring
  have hcb : ∀ e < 1869,
      4 * |(sourcePoly pR (fun i => ι (z i + 1))).coeff e| + 4 ≤ ι (Exp.exp v) := by
    intro e _
    rw [hBv]
    refine le_trans (coeff_bound pR _ Hc hb1 hH8 (hBb _) hc _ (fun i => ι_nonneg _)
      (fun i => ?_) e) ?_
    · exact ι_le_ι.2 (lt_iff_succ_le.mp (hz i))
    · rw [Bq, baseScale_eq]; exact hBc _
  have hT : AT (ι (Exp.exp k)) = ∑ e ∈ Finset.range 1869,
      (if LowMask.Pos targets e then (1 : DiffRing V) else 0) * Bc (ι (Exp.exp k)) ^ e := by
    rw [AT, sum_range_table targets targets_injective 1869 targets_lt]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [if_pos ⟨r, rfl⟩, one_mul]
    · intro j _ hp
      rw [if_neg (fun ⟨r, hr⟩ => hp r hr), zero_mul]
  have hX : ι (TstN (Bcm (Exp.exp k)) + 2 * G) =
      ∑ e ∈ Finset.range 1869,
        (2 * (sourcePoly pR (fun i => ι (z i + 1))).coeff e +
          if LowMask.Pos targets e then 1 else 0) * ι (Exp.exp v) ^ e := by
    rw [map_add, map_mul, map_ofNat, ι_TstN, hG, coded_sum pR _ _ _ hu, hBv, hT, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have key := SignedDigits.high_noCarry_iff v hv1 1869 (LowMask.Pos targets)
    (fun e => (sourcePoly pR (fun i => ι (z i + 1))).coeff e) hcb _ hX
  have hmask : highMask (Bcm (Exp.exp k)) =
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

/-! ## The contract -/

/-- **The central-binomial contract of package 106.** -/
theorem contract (k g X Y : V) (hgc : ι g < 4 * cap (ι (Exp.exp k))) (h4 : 4 ∣ g)
    (hX : ι X = Xc pR (ι (Exp.exp k)) (ι g)) (hY : ι Y = Yc (ι (Exp.exp k))) :
    Y ∣ binom (2 * X) X ↔
      ∃ z : Fin 31 → V, (∀ i, z i < Exp.exp k) ∧ g = ∑ i, z i * Bcm (Exp.exp k) ^ weights i ∧
        ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  obtain ⟨hH8, hc⟩ := port_facts (V := V)
  have hb1 := one_le_ι (exp_pos k)
  obtain ⟨hGpos, -, -, -, -, -⟩ := prefix_pos (Exp.exp k) g (exp_pos k)
  obtain ⟨v, hv⟩ : ∃ v : V, v = 2134940 + k + k := ⟨_, rfl⟩
  obtain ⟨hkv, hv1, hBm⟩ := v_facts k v hv
  have hBv : ι (Exp.exp v) = Bc (ι (Exp.exp k)) := by rw [← hBm, ι_Bcm]
  have hB2 : 2 ≤ Bcm (Exp.exp k) := by
    apply ι_le_ι.mp
    rw [map_ofNat, ι_Bcm]
    obtain ⟨hB32, -⟩ := scale_facts (ι (Exp.exp k)) Hc hb1 hH8 (hBc _)
    linarith
  obtain ⟨hSTL, hgN, hmN⟩ := sum_lt pR (ι (Exp.exp k)) (ι g) Hc hb1 hH8 (hBc _) hc
    (ι_nonneg g) hgc
  obtain ⟨G, hG⟩ := nonneg_iff.mp hGpos.le
  obtain ⟨K117, hK117d⟩ : ∃ K : V, K = 117 * v := ⟨_, rfl⟩
  have hK117 : Exp.exp K117 = Exp.exp v ^ 117 := by rw [hK117d, exp_mul_lit]
  have hιK : ι (Exp.exp K117) = N0 (ι (Exp.exp k)) := by rw [hK117, map_pow, hBv, N0]
  obtain ⟨q, hq⟩ := lowMask_four_three k v hv
  obtain ⟨X', hXd⟩ : ∃ X' : V, X' = TstN (Exp.exp v) + 2 * G := ⟨_, rfl⟩
  obtain ⟨Sn, hSd⟩ : ∃ S : V, S = g + X' * Exp.exp K117 := ⟨_, rfl⟩
  obtain ⟨Tn, hTd⟩ : ∃ T : V, T = 4 * q + 1 + highMask (Exp.exp v) * Exp.exp K117 := ⟨_, rfl⟩
  have hlowι : ι (lowMask (Exp.exp k) (Exp.exp v)) = mask (ι (Exp.exp k)) := by
    have h := congrArg ι (lowMask_dsum k v hkv)
    simp only [map_add, map_mul, map_one, map_sum, map_pow, P72Root.ι_tsub (one_le_exp k),
      hBv] at h
    rw [Z10Regs.mask, N0, ell]
    linear_combination h
  have h4q : ι (4 * q + 1) = mask (ι (Exp.exp k)) - 2 := by
    rw [← hlowι, hq]
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring
  have hXι : ι X' = AT (ι (Exp.exp k)) + 2 * coded pR (ι (Exp.exp k)) (ι g) := by
    rw [hXd, map_add, map_mul, map_ofNat, ← hBm, ι_TstN, ← hG]
  have hSι : ι Sn = Sc pR (ι (Exp.exp k)) (ι g) := by
    rw [hSd, map_add, map_mul, hXι, hιK, Sc]; ring
  have hTι : ι Tn = Tc (ι (Exp.exp k)) := by
    rw [hTd, map_add, map_mul, h4q, hιK, ← hBm, ι_highMask _ hB2, Tc]; ring
  obtain ⟨u, hud⟩ : ∃ u : V, u = 1986 * v := ⟨_, rfl⟩
  have hu : ι (Exp.exp u) = NN (ι (Exp.exp k)) := by
    rw [hud, exp_mul_lit, map_pow, hBv, NN]
  obtain ⟨m, hmd⟩ : ∃ m : V, m = k + 34159017 + 2109 * v := ⟨_, rfl⟩
  have hYm : Y = Exp.exp m := by
    apply ι_injective
    rw [hY, Yc, threshold_eq', hmd, exp_add, exp_add, exp_mul_lit, map_mul, map_mul, map_pow,
      hBv]
    ring
  have hST : Sn + Tn < Exp.exp u := by
    apply ι_lt_ι.mp; rw [map_add, hSι, hTι, hu]; exact hSTL
  have hRe : X + Sn + 1 = Exp.exp u * (Sn + Tn + 1) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [hX, hSι, hTι, hu, Xc]; ring
  have hlowlt : lowMask (Exp.exp k) (Exp.exp v) < Exp.exp K117 := by
    apply ι_lt_ι.mp; rw [hlowι, hιK]; exact hmN
  have hlow1 : 4 * q + 1 < Exp.exp K117 := by
    refine lt_of_le_of_lt ?_ hlowlt
    rw [hq]
    exact add_le_add le_rfl (by norm_num)
  have hpopT : population Tn =
      population (highMask (Exp.exp v)) + population (4 * q + 1) := by
    rw [hTd, add_comm (4 * q + 1), ArithmeticBinaryPopulation.concatenate _ _ _ hlow1]
  have hm : m = u + population Tn := by
    have h1' := congrArg ι (pop_low k v hkv)
    have h2' := congrArg ι (pop_high v hv1)
    have h3' := congrArg ι (population_low q)
    have hvι := congrArg ι hv
    rw [hq] at h1'
    rw [hpopT, hmd, hud]
    apply ι_injective
    simp only [map_add, map_mul, map_ofNat, map_one] at h1' h2' h3' hvι ⊢
    linear_combination -h1' - h2' + h3' - 16 * hvι
  have hcal := noCarry_iff_exp_dvd_sparse hST hRe hm
  rw [hYm, ← hcal]
  have hgK : g < Exp.exp K117 := by apply ι_lt_ι.mp; rw [hιK]; exact hgN
  rw [hSd, hTd, ← noCarry_concat hgK hlow1]
  obtain ⟨a, ha⟩ := h4
  have hlowiff : NoCarry g (4 * q + 1) ↔ NoCarry g (lowMask (Exp.exp k) (Exp.exp v)) := by
    rw [hq, ha]; exact noCarry_low a q
  have hg117 : g < Exp.exp v ^ 117 := by rw [← hK117]; exact hgK
  rw [hlowiff, lowMask,
    LowMask.noCarry_code_iff_weights hkv weights weights_injective 117 weights_lt g hg117,
    hBm, hXd]
  constructor
  · rintro ⟨⟨z, hz, hgz⟩, hhigh⟩
    refine ⟨z, hz, hgz, ?_⟩
    have hGz : ι G = coded pR (ι (Exp.exp k)) (ι (∑ i, z i * Bcm (Exp.exp k) ^ weights i)) := by
      rw [hBm, ← hgz]; exact hG.symm
    have h := (high_iff k z hz G hGz).mp
    rw [hBm] at h
    exact h hhigh
  · rintro ⟨z, hz, hgz, hrows⟩
    refine ⟨⟨z, hz, hgz⟩, ?_⟩
    have hGz : ι G = coded pR (ι (Exp.exp k)) (ι (∑ i, z i * Bcm (Exp.exp k) ^ weights i)) := by
      rw [hBm, ← hgz]; exact hG.symm
    have h := (high_iff k z hz G hGz).mpr hrows
    rw [hBm] at h
    exact h

#print axioms lowMask_four_three
#print axioms high_iff
#print axioms contract

end DiophantineConsistency.Z10Contract
