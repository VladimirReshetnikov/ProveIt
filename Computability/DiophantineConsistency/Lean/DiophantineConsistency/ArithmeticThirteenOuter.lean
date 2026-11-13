import DiophantineConsistency.ArithmeticWindowZero
import DiophantineConsistency.ArithmeticHalfBinomial2011
import DiophantineConsistency.ArithmeticRankForcing2011
import DiophantineConsistency.ModelArithmetic
/-! # Outer facts of an arbitrary Carrier65 zero in every model of `𝗜𝚺₁`

Internal counterparts of the two facts `ThirteenCarrierComplete.outer_facts`
derives from native source analysis over `ℤ`, now for an arbitrary positive
zero in a nonstandard model:

* `base_lt_shift`: the spatial shift `w` exceeds the base `q`, from the radix
  decomposition `q = 2^{WL}`, `w = 2^{rank-WL}` and `3WL+1 ≤ rank`;
* `rank_mod_four`: `rank ≡ 3 (mod 4)`, from `4 ∣ q`, the window origin
  `C ≡ 1 (mod 2^47)`, `MC ≡ 2 (mod 4)` and oddness of `J` (forced by
  `q = βJ + 1`), computed with the mod-4 homomorphism of the ring of
  differences. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.ArithmeticThirteenOuter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011 ModelDifferenceRing
open DiscreteOrderedRingFacts ModelArithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b := by
  have e := congrArg (ι : V →+* DiffRing V) (tsub_add_cancel_of_le h)
  rw [map_add] at e
  linear_combination e

theorem width_pos : (0 : V) < (CurrentMasks2011.width : V) := by
  have : 0 < CurrentMasks2011.width := by unfold CurrentMasks2011.width; decide
  exact_mod_cast this

/-- The spatial shift exceeds the base at every positive zero. -/
theorem base_lt_shift (u : Fin 14 → V) (h : PositiveZero u) : q u < u 8 := by
  obtain ⟨L, hL, hq, _, hw, _, _⟩ := (current_radix u h.1 h.2).2
  have h3 := ArithmeticHalfBinomial2011.three_h_lt_rank u h.1 _ hq
  rw [hq, hw]
  apply exp_monotone.mpr
  set WL := (CurrentMasks2011.width : V) * L
  apply lt_tsub_iff_left.mpr
  calc WL + WL ≤ WL + WL + WL := le_self_add
    _ = 3 * WL := by ring
    _ < 3 * WL + 1 := lt_add_of_pos_right _ _root_.zero_lt_one
    _ ≤ rank u := h3

/-- `mod4` sends `4k + m` to `m`. -/
theorem mod4_val {x k : V} {m : ℕ} (h : x = 4*k + m) : mod4 (ι x) = (m : ZMod 4) := by
  have e : ι x = ((4 : ℕ) : DiffRing V) * ι k + (m : DiffRing V) := by
    rw [h]; simp only [map_add, map_mul, map_natCast, map_ofNat, Nat.cast_ofNat]
  rw [e]
  exact residue_natCast_add model_discrete (model_residues 4) (ι k) m

/-- `mod4 (ι x) = 0` when `4 ∣ x`. -/
theorem mod4_of_dvd {x : V} (h : 4 ∣ x) : mod4 (ι x) = 0 := by
  obtain ⟨k, hk⟩ := h
  have := mod4_val (x := x) (k := k) (m := 0) (by rw [hk]; simp)
  simpa using this

/-- `x % 4 = r` from the value of `mod4 (ι x)`. -/
theorem mod_four_of_mod4 {x : V} {r : ℕ} (hr : r < 4) (h : mod4 (ι x) = (r : ZMod 4)) :
    x % 4 = r := by
  obtain ⟨m, hm, hxm⟩ := exists_nat_of_lt (x % 4) 4 (mod_lt x (by norm_num))
  have hx : x = 4*(x/4) + m := by rw [← hxm]; exact (div_add_mod x 4).symm
  have hv := mod4_val hx
  rw [h] at hv
  have hmr : m = r := by
    have := congrArg ZMod.val hv
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hr] at this
    exact this.symm
  rw [hxm, hmr]

theorem four_dvd_exp {e : V} (he : 2 ≤ e) : (4 : V) ∣ Exp.exp e := by
  obtain ⟨d, rfl⟩ := exists_add_of_le he
  refine ⟨Exp.exp d, ?_⟩
  rw [add_comm, show d + 2 = d + 1 + 1 by ring, exp_succ, exp_succ]
  ring

/-- The window coordinate `C = q - F - α` is positive, so `F < q` and `α < q - F`. -/
theorem window_positive (u : Fin 14 → V) (h : PositiveZero u) :
    u 2 < q u - u 1 ∧ u 1 < q u := by
  obtain ⟨N, _, hwin⟩ := ArithmeticWindowZero.window_of_positive_zero u h
  have horig := hwin.origin
  rw [ArithmeticWindowDigits.dig_zero_index] at horig
  have hCpos : 0 < q u - u 1 - u 2 := by
    by_contra h0; push_neg at h0
    have h00 : q u - u 1 - u 2 = 0 := le_antisymm h0 (_root_.zero_le)
    rw [h00] at horig; simp at horig
  have hαlt : u 2 < q u - u 1 := tsub_pos_iff_lt.mp hCpos
  exact ⟨hαlt, tsub_pos_iff_lt.mp (lt_of_le_of_lt (_root_.zero_le) hαlt)⟩

/-- The rank is `3` modulo `4` at every positive zero. -/
theorem rank_mod_four (u : Fin 14 → V) (h : PositiveZero u) : rank u % 4 = 3 := by
  -- the base is a multiple of four
  obtain ⟨L, hL, hqL, _, _, _, _⟩ := (current_radix u h.1 h.2).2
  have hWL : 2 ≤ (CurrentMasks2011.width : V) * L := by
    have hW : (2 : V) ≤ (CurrentMasks2011.width : V) := by
      have : 2 ≤ CurrentMasks2011.width := by unfold CurrentMasks2011.width; decide
      exact_mod_cast this
    calc (2 : V) = 2 * 1 := (mul_one 2).symm
      _ ≤ (CurrentMasks2011.width : V) * L := mul_le_mul hW (pos_iff_one_le.mp hL) (by simp) (by simp)
  have hq0 : mod4 (ι (q u)) = 0 := mod4_of_dvd (by rw [hqL]; exact four_dvd_exp hWL)
  -- the window origin: C ≡ 1 (mod 4)
  obtain ⟨N, _, hwin⟩ := ArithmeticWindowZero.window_of_positive_zero u h
  have horig := hwin.origin
  rw [ArithmeticWindowDigits.dig_zero_index] at horig
  have hC : q u - u 1 - u 2 = 4*((Exp.exp (45:V)) * ((q u - u 1 - u 2) / Exp.exp 47)) + (1 : ℕ) := by
    have e := (div_add_mod (q u - u 1 - u 2) (Exp.exp 47)).symm
    rw [horig] at e
    generalize (q u - u 1 - u 2) / Exp.exp 47 = Q at e ⊢
    have h47 : Exp.exp (47 : V) = 4 * Exp.exp 45 := by
      rw [show (47 : V) = 45 + 1 + 1 by norm_num, exp_succ, exp_succ]; ring
    rw [h47] at e
    rw [Nat.cast_one]
    linear_combination e
  have hC1 := mod4_val hC
  obtain ⟨hαlt, hFlt⟩ := window_positive u h
  have hCι : ι (q u - u 1 - u 2) = ι (q u) - ι (u 1) - ι (u 2) := by
    rw [ι_tsub hαlt.le, ι_tsub hFlt.le]
  rw [hCι] at hC1
  simp only [map_sub, hq0, Nat.cast_one] at hC1
  -- the low port is 2 modulo 4
  have hMC : mod4 (ι (CurrentMasks2011.lowPort : V)) = 2 := by
    have hlp := ArithmeticRankForcing2011.lowPort_mod_four (V := V)
    generalize (CurrentMasks2011.lowPort : V) = Lp at hlp ⊢
    have h0 := (div_add_mod Lp 4).symm
    rw [hlp] at h0
    have hx : Lp = 4 * (Lp / 4) + ((2 : ℕ) : V) := by exact_mod_cast h0
    have := mod4_val hx
    exact_mod_cast this
  -- the base factor: beta * J = q - 1
  have hq1 : 1 ≤ q u := by
    show 1 ≤ (CurrentMasks2011.beta:V) * u 0 + 1; exact le_add_self
  have hbJ : mod4 (ι ((CurrentMasks2011.beta:V) * u 0)) = -1 := by
    have : (CurrentMasks2011.beta:V) * u 0 = q u - 1 := by
      rw [show q u = (CurrentMasks2011.beta:V) * u 0 + 1 from rfl, add_tsub_cancel_right]
    rw [this, ι_tsub hq1, map_sub, hq0, map_one, map_one, _root_.zero_sub]
  have hJodd : 2 * mod4 (ι (u 0)) = 2 := by
    rw [map_mul, map_mul] at hbJ
    revert hbJ
    generalize mod4 (ι (CurrentMasks2011.beta : V)) = a
    generalize mod4 (ι (u 0)) = j
    revert a j; decide
  -- the rank
  have hq2 : 1 ≤ q u ^ 2 := one_le_pow₀ hq1
  have hrank : ι (rank u) = ((ι (q u) - 1) * (ι (q u) - ι (u 1)) + ι (u 2)) * (ι (q u) ^ 2 - 1) +
      (ι (CurrentMasks2011.lowPort : V) +
        ι (q u) * ι (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V))) * ι (u 0) := by
    unfold rank
    rw [map_add, map_mul, map_mul, map_add, map_mul, ι_tsub hq1, ι_tsub hFlt.le, ι_tsub hq2,
      map_one, map_pow, map_add, map_mul]
  apply mod_four_of_mod4 (by norm_num)
  rw [hrank]
  simp only [map_add, map_mul, map_sub, map_pow, map_one, hq0, hMC]
  have hFα : mod4 (ι (u 1)) + mod4 (ι (u 2)) = -1 := by linear_combination -hC1
  push_cast
  linear_combination -hFα + hJodd

end DiophantineConsistency.ArithmeticThirteenOuter
