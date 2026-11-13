import DiophantineConsistency.Mixed121.Mixed121Word
import DiophantineConsistency.Mixed121.Mixed121KernelSplit
import DiophantineConsistency.Mixed121.Mixed121Clean
import DiophantineConsistency.ArithmeticPacking

/-! # Transport blocks of the packed 121x8801 word

The 121x8801 counterpart of Compact44's `CompactKernelLowProduct`,
`CompactKernelBlockSize`, `CompactWordPhaseZeroHigh`,
`CompactWordCleanSupport`, `CompactWordPulseEquality`, `CompactWordLowSlot` and
the digit part of `CompactConstructedCarryInput`, with their theorem names.

For a cell (or a pulsed cell) `x < 2^(121·3297+1)` and `B = 2^1064921`:

* `K·x mod B` is `lower·x < 2^(121·8793+1)`, and `K·x / B = 2^(121·42)·x`,
  because `K = ρ^8843 + lower` with `ρ^8843 = B·2^(121·42)`;
* so a cell plus its transport block `blk` stays below `B`
  (`cell_sum_of_small`);
* at high-mask phase `0` (digit `4`) every block is carry-free: `8 ∣ K`,
  `8 ∣ 2^(121·42)`, and a cell is `0` or `1` modulo `8`;
* a packed word has no digit outside the `Bad` hull and is carry-free
  against `MC` slot by slot. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Mixed121Block
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks
  ArithmeticBinaryCarry ArithmeticPacking
open CompactMarkedTransport Mixed121Kernel Mixed121KernelSplit Mixed121Cell Mixed121Word
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem high_origin : dig 121 ((Mixed121Ports.highNat : ℕ) : V) 0 = 4 := by
  have h := ArithmeticMaskConstants.dig_ofDigits (V:=V) 121 Mixed121Ports.highDigits
    Mixed121Masks.high_digit_lt 0
  have hh : Mixed121Ports.highDigits.getD 0 0 = 4 := by decide +kernel
  rw [hh] at h
  rw [Mixed121Masks.highNat_eq]
  exact h

attribute [local irreducible] paramKernel rho lowerKernelAt Mixed121Ports.lowNat Mixed121Ports.highNat

/-! ## The kernel product -/

theorem rho_pow_cast (n : ℕ) : ((rho ^ n : ℕ) : V) = Exp.exp ((121*n : ℕ) : V) := by
  have he : rho ^ n = 2 ^ (121*n) := by unfold rho; rw [← pow_mul]
  rw [he, ← cast_exp]

theorem kernel_split_model :
    (paramKernel rho : V) = Exp.exp (121*8843 : V) + ((lowerKernelAt rho : ℕ) : V) := by
  have he := congrArg (fun n : ℕ => (n : V)) (kernel_split_generic rho)
  rw [Nat.cast_add, rho_pow_cast] at he
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using he

theorem lower_bound_model :
    ((lowerKernelAt rho : ℕ) : V) < Exp.exp (121*5496 : V) := by
  have h : ((lowerKernelAt rho : ℕ) : V) < ((rho ^ 5496 : ℕ) : V) := by
    exact_mod_cast lower_lt
  rw [rho_pow_cast] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

theorem low_product_lt (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp (121*8793+1 : V) := by
  calc
    ((lowerKernelAt rho : ℕ) : V) * x ≤ Exp.exp (121*5496 : V) * x :=
      mul_le_mul_of_nonneg_right lower_bound_model.le (Arithmetic.zero_le x)
    _ < Exp.exp (121*5496 : V) * Exp.exp (121*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((121*5496)+(121*3297+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (121*8793+1 : V) := by
      apply congrArg Exp.exp
      norm_num

private theorem top_split : Exp.exp (121*8843 : V) = Exp.exp 1064921 * Exp.exp (121*42 : V) := by
  rw [← exp_add]
  congr 1
  norm_num

theorem low_product_remainder (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    ((paramKernel rho : V) * x) % Exp.exp 1064921 = ((lowerKernelAt rho : ℕ) : V) * x := by
  have hlo := low_product_lt x hx
  have hbase : ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp 1064921 :=
    lt_of_lt_of_le hlo (exp_monotone_le.mpr (by norm_num : (121*8793+1 : V) ≤ 1064921))
  rw [kernel_split_model, top_split]
  have hm : (Exp.exp 1064921 * Exp.exp (121*42) + ((lowerKernelAt rho : ℕ) : V)) * x =
      ((lowerKernelAt rho : ℕ) : V) * x + Exp.exp 1064921 * (Exp.exp (121*42) * x) := by ring
  rw [hm, mod_add_mul' _ _ (exp_pos (1064921:V)), mod_eq_self_of_lt hbase]

/-- The high half comes exclusively from the isolated top kernel digit. -/
theorem high_product (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    ((paramKernel rho : V) * x) / Exp.exp 1064921 = Exp.exp (121*42) * x := by
  have hlo := low_product_lt x hx
  have hbase : ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp 1064921 :=
    lt_of_lt_of_le hlo (exp_monotone_le.mpr (by norm_num : (121*8793+1 : V) ≤ 1064921))
  rw [kernel_split_model, top_split]
  have hm : (Exp.exp 1064921 * Exp.exp (121*42) + ((lowerKernelAt rho : ℕ) : V)) * x =
      (Exp.exp (121*42) * x) * Exp.exp 1064921 + ((lowerKernelAt rho : ℕ) : V) * x := by ring
  rw [hm, div_mul_add _ _ hbase]

theorem high_product_lt (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    ((paramKernel rho : V) * x) / Exp.exp 1064921 < Exp.exp (121*3339+1 : V) := by
  rw [high_product x hx]
  calc
    Exp.exp (121*42 : V) * x < Exp.exp (121*42 : V) * Exp.exp (121*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((121*42)+(121*3297+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (121*3339+1 : V) := by apply congrArg Exp.exp; norm_num

/-- Pointwise size alone suffices for the full cell-plus-transport-block bound. -/
theorem cell_sum_of_small {N s : V} {X : V → V}
    (hN : 0 < N) (hsmall : ∀ j < N, X j < Exp.exp (121*3297+1 : V)) :
    ∀ j < N, X j + blk 1064921 (paramKernel rho : V) N s X j < Exp.exp 1064921 := by
  intro j hj
  have h0 := hsmall j hj
  have h1 := hsmall (cyc N j 1) (cyc_lt hN j 1)
  have hs := hsmall (cyc N j s) (cyc_lt hN j s)
  let E : V := Exp.exp (121*8793+1)
  have hx : X j < E := lt_of_lt_of_le h0 (exp_monotone_le.mpr (by norm_num))
  have hs' : X (cyc N j s) < E := lt_of_lt_of_le hs (exp_monotone_le.mpr (by norm_num))
  have hl : lo 1064921 (paramKernel rho : V) X j < E := by
    unfold lo E
    rw [low_product_remainder (X j) h0]
    exact low_product_lt (X j) h0
  have hh : hi 1064921 (paramKernel rho : V) X (cyc N j 1) < E := by
    unfold hi E
    exact lt_of_lt_of_le (high_product_lt _ h1) (exp_monotone_le.mpr (by norm_num))
  have hsum : X j + (lo 1064921 (paramKernel rho : V) X j +
      hi 1064921 (paramKernel rho : V) X (cyc N j 1) + X (cyc N j s)) < E+E+E+E := by
    have ha := add_lt_add hx hl
    have hb := add_lt_add hh hs'
    calc
      _ = (X j + lo 1064921 (paramKernel rho : V) X j) +
          (hi 1064921 (paramKernel rho : V) X (cyc N j 1) + X (cyc N j s)) := by ring
      _ < (E+E)+(E+E) := add_lt_add ha hb
      _ = E+E+E+E := by ring
  have hfour : E+E+E+E = Exp.exp (121*8793+3 : V) := by
    have he : Exp.exp ((121*8793+1)+1+1 : V) =
        2*(2*Exp.exp (121*8793+1 : V)) := by rw [exp_succ, exp_succ]
    calc
      E+E+E+E = 2*(2*Exp.exp (121*8793+1 : V)) := by unfold E; ring
      _ = Exp.exp ((121*8793+1)+1+1 : V) := he.symm
      _ = Exp.exp (121*8793+3 : V) := by apply congrArg Exp.exp; ring
  rw [hfour] at hsum
  exact lt_of_lt_of_le (by simpa [blk] using hsum)
    (exp_monotone_le.mpr (by norm_num : (121*8793+3 : V) ≤ 1064921))

/-! ## High-mask phase zero -/

theorem eight_dvd_exp {e : V} (he : 3 ≤ e) : (8 : V) ∣ Exp.exp e := by
  obtain ⟨d, rfl⟩ := exists_add_of_le he
  refine ⟨Exp.exp d, ?_⟩
  rw [add_comm, show d+3=d+1+1+1 by ring, exp_succ, exp_succ, exp_succ]
  ring

theorem kernel_dvd_eight : (8 : V) ∣ (paramKernel rho : V) := by
  have hr : 8 ∣ rho := by unfold rho; norm_num
  have hr0 : 2^121 ≤ rho := by unfold rho; exact le_rfl
  have hn : 8 ∣ paramKernel rho :=
    dvd_trans hr (Nat.dvd_of_mod_eq_zero (kernel_mod_radix_generic rho hr0))
  have h := cast_mod (V:=V) (paramKernel rho) 8
  rw [Nat.mod_eq_zero_of_dvd hn] at h
  apply mod_eq_zero_iff_dvd.mp
  simpa using h.symm

/-- A cell has only its Boolean selector-zero bit below bit 121. -/
theorem cell_mod_eight (a d : V) (hd : d ≤ 1) : packedCell a d % 8 ≤ 1 := by
  have hs := packedCell_digit a d 0 hd (by norm_num)
  rw [dig_zero_index] at hs
  have hb : packedCell a d % Exp.exp 121 ≤ 1 := by
    rw [hs]
    exact cellDigit_le_one a d 0 hd
  have hm := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<8)
    (eight_dvd_exp (by norm_num : (3:V)≤121)) (packedCell a d)
  rw [mod_eq_self_of_lt (lt_of_le_of_lt hb (by norm_num))] at hm
  rw [← hm]
  exact hb

theorem low_dvd_eight (x : V) : (8:V) ∣ ((paramKernel rho : V)*x % Exp.exp 1064921) := by
  have hp : (8:V) ∣ (paramKernel rho : V)*x := dvd_mul_of_dvd_left kernel_dvd_eight _
  have hm := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<8)
    (eight_dvd_exp (by norm_num : (3:V)≤1064921)) ((paramKernel rho : V)*x)
  apply mod_eq_zero_iff_dvd.mp
  rw [hm, mod_eq_zero_iff_dvd.mpr hp]

theorem high_dvd_eight (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    (8:V) ∣ ((paramKernel rho : V)*x / Exp.exp 1064921) := by
  rw [high_product x hx]
  exact dvd_mul_of_dvd_left (eight_dvd_exp (by norm_num : (3:V)≤121*42)) _

/-- A number congruent to zero or one modulo eight cannot overlap bit two. -/
theorem noCarry_four_of_mod_eight (x : V) (hx : x % 8 ≤ 1) : NoCarry x 4 := by
  have h8 : Exp.exp (3:V) = 8 := by simpa using cast_exp (V:=V) 3
  have hl : NoCarry (x % 8) (4:V) := by
    rcases le_one_iff_eq_zero_or_one.mp hx with hz | ho
    · rw [hz, noCarry_iff]; intro i; simp
    · rw [ho]
      apply one_noCarry_even
      apply mod_eq_zero_iff_dvd.mpr
      exact ⟨2, by norm_num⟩
  have hh : NoCarry (x / 8) (0:V) := by rw [noCarry_iff]; intro i; simp
  have ha : x%8 < Exp.exp (3:V) := by rw [h8]; exact mod_lt _ (by norm_num)
  have hb : (4:V) < Exp.exp 3 := by rw [h8]; norm_num
  have h := noCarry_concat ha hb hl hh
  have he : (x/8)*Exp.exp (3:V) + x%8 = x := by
    rw [h8, mul_comm]; exact div_add_mod x 8
  rw [he] at h
  simpa only [zero_mul, zero_add] using h

/-- Every physical block has no carry at high-mask phase zero. -/
theorem phase_zero_noCarry {row dummy : V → V} {N s j : V}
    (hw : CompactWord row N s) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (dummy k)) j) 0) (dig 121 ((Mixed121Ports.highNat : ℕ) : V) 0) := by
  let X : V → V := fun k => normalizedCell (row k) (dummy k)
  have hk : cyc N j 1 < N := cyc_lt hw.pos j 1
  have hd (k : V) : dummy k % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have hsmall : X (cyc N j 1) < Exp.exp (121*3297+1 : V) := by
    exact lt_of_lt_of_le (packedCell_lt_support (row (cyc N j 1)) (dummy (cyc N j 1)%2)
      (hw.tile_ne _ hk) (hd _)) (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hlo : (8:V) ∣ lo 1064921 (paramKernel rho : V) X j := low_dvd_eight _
  have hhi : (8:V) ∣ hi 1064921 (paramKernel rho : V) X (cyc N j 1) := high_dvd_eight _ hsmall
  have hsum : (blk 1064921 (paramKernel rho : V) N s X j) % 8 ≤ 1 := by
    change (lo 1064921 (paramKernel rho : V) X j +
      hi 1064921 (paramKernel rho : V) X (cyc N j 1) + X (cyc N j s)) % 8 ≤ 1
    rw [mod_add_remove_left_of_dvd (dvd_add hlo hhi) (by norm_num)]
    exact cell_mod_eight (row (cyc N j s)) (dummy (cyc N j s)%2) (hd _)
  have hm := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<8)
    (eight_dvd_exp (by norm_num : (3:V)≤121)) (blk 1064921 (paramKernel rho : V) N s X j)
  have hdigit : (dig 121 (blk 1064921 (paramKernel rho : V) N s X j) 0) % 8 ≤ 1 := by
    rw [dig_zero_index, hm]
    exact hsum
  rw [high_origin]
  exact noCarry_four_of_mod_eight _ hdigit

/-! ## Clean support -/

theorem cell_outside_bad (a d p : V) (ha : a ≠ 1) (hp : p < 8801)
    (hbad : ¬ Mixed121Clean.Bad p) : cellDigit a d p = 0 := by
  by_contra hn
  obtain ⟨n, he, hs⟩ := cellDigit_supported a d p ha hp hn
  have hb : Mixed121Clean.Bad (n : V) := (Mixed121Clean.bad_cast n).2 (Mixed121Clean.support_subset_bad n hs)
  apply hbad
  rw [he]
  exact hb

theorem word_outside_bad (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (k : V) (hk : k < 8801*N)
    (hbad : ¬ Mixed121Clean.Bad (k%8801)) : dig 121 (packedWord row dummy N) k = 0 := by
  have hj : k/8801 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8801 < 8801 := mod_lt k (by norm_num)
  have he : 8801*(k/8801)+k%8801 = k := div_add_mod k 8801
  rw [← he, word_digit row dummy N _ _ hj hp]
  exact cell_outside_bad (row (k/8801)) (dummy (k/8801)%2) _ (hw.tile_ne _ hj) hp hbad

/-! ## Pulses and low slots -/

theorem cellWord_pulse (row dummy : V → V) (j : V) :
    cellWord row dummy j = packedCell (row j) 0 + Exp.exp (121*1063) * (dummy j % 2) :=
  normalized_eq_pulse _ _

theorem cellWord_boolean_pulse (row dummy : V → V) (j : V) (hd : dummy j ≤ 1) :
    cellWord row dummy j = packedCell (row j) 0 + Exp.exp (121*1063) * dummy j := by
  rw [cellWord_pulse, mod_eq_self_of_lt (lt_two_iff_le_one.mpr hd)]

theorem packedWord_pulses (row dummy : V → V) (N : V) :
    packedWord row dummy N =
      bsum (121*8801) (fun j => packedCell (row j) 0 + Exp.exp (121*1063) * (dummy j % 2)) N := by
  unfold packedWord
  congr 1
  funext j
  exact cellWord_pulse row dummy j

/-- The represented block sum has precisely the cell's subdigits. -/
theorem packed_digit (X : V → V) [𝚺₁-Function₁ X] (N j p : V)
    (hX : ∀ j<N, X j<Exp.exp (121*8801)) (hj : j<N) (hp : p<8801) :
    dig 121 (bsum (121*8801) X N) (8801*j+p) = dig 121 (X j) p := by
  rw [← subdigit _ _ _ hp, dig_bsum hX hj]

/-- Cell-wise digit cap transfers to the entire packed source word. -/
theorem packed_cap (X : V → V) [𝚺₁-Function₁ X] (N : V)
    (hX : ∀ j<N, X j<Exp.exp (121*8801))
    (hcap : ∀ j<N, ∀ p<8801, dig 121 (X j) p≤3) :
    ∀ k<8801*N, dig 121 (bsum (121*8801) X N) k≤3 := by
  intro k hk
  have hj : k/8801<N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8801<8801 := mod_lt k (by norm_num)
  have he : 8801*(k/8801)+k%8801=k := div_add_mod k 8801
  rw [←he, packed_digit X N _ _ hX hj hp]
  exact hcap _ hj _ hp

/-- Every valid base or pulsed cell is disjoint from `MC`. -/
theorem cell_low {row dummy : V → V} {N s j : V}
    (hw : CompactWord row N s) (hj : j < N) (hbool : dummy j ≤ 1) :
    NoCarry (cellWord row dummy j) ((Mixed121Ports.lowNat : ℕ) : V) := by
  have hbase := base_noCarry (row j) (hw.tile_ne j hj)
  have hpulse := packedCell_pulse_noCarry (row j) hbase
  rw [cellWord_boolean_pulse row dummy j hbool]
  rcases le_one_iff_eq_zero_or_one.mp hbool with hz | ho
  · simpa only [hz, mul_zero, add_zero] using hbase
  · simpa only [ho, mul_one] using hpulse

/-- Slotwise no-carry against `MC` for the actual packed word. -/
theorem word_low_slots (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hbool : ∀ j, dummy j ≤ 1) :
    ∀ k < 8801*N, NoCarry (dig 121 (packedWord row dummy N) k)
      (dig 121 ((Mixed121Ports.lowNat : ℕ) : V) (k%8801)) := by
  let X : V → V := cellWord row dummy
  letI : 𝚺₁-Function₁ X := word_definable row dummy
  have hX : ∀ j < N, X j < Exp.exp (121*8801) := fun j _ => word_cell_lt row dummy j
  intro k hk
  have hj : k/8801 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8801 < 8801 := mod_lt k (by norm_num)
  have he : 8801*(k/8801)+k%8801 = k := div_add_mod k 8801
  have hd : dig 121 (packedWord row dummy N) k = dig 121 (X (k/8801)) (k%8801) := by
    calc
      dig 121 (packedWord row dummy N) k =
          dig 121 (packedWord row dummy N) (8801*(k/8801)+k%8801) := by rw [he]
      _ = dig 121 (X (k/8801)) (k%8801) := packed_digit X N _ _ hX hj hp
  rw [hd]
  exact noCarry_dig 121 (X (k/8801)) ((Mixed121Ports.lowNat : ℕ) : V) (k%8801)
    (cell_low hw hj (hbool (k/8801)))

#print axioms Mixed121Block.high_product
#print axioms Mixed121Block.cell_sum_of_small
#print axioms Mixed121Block.phase_zero_noCarry
#print axioms Mixed121Block.word_outside_bad
#print axioms Mixed121Block.word_low_slots
end Mixed121Block
