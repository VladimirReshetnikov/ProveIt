import DiophantineConsistency.ArithmeticThirteenOuter
import DiophantineConsistency.Adm942.Adm942WindowZero
import DiophantineConsistency.Adm942.Adm942RankForcing

/-! # Outer facts of an arbitrary admissible942 zero in every model of `𝗜𝚺₁`

The counterpart of `ArithmeticThirteenOuter` at the admissible942 ports
(`β = 2^189269 − 1`, width `189269 = 47·4027`):

* `base_lt_shift`: the spatial shift `w` exceeds the base `q`, from the radix
  decomposition `q = 2^{WL}`, `w = 2^{rank-WL}` and `3WL+1 ≤ rank`
  (`Adm942HalfBinomial.three_h_lt_rank`);
* `window_positive`: `C = q - F - α > 0`, from the window origin
  (`Adm942WindowZero.window_of_positive_zero`);
* `rank_mod_four`: `rank ≡ 3 (mod 4)`, from `4 ∣ q`, the window origin
  `C ≡ 1 (mod 2^47)`, `MC ≡ 2 (mod 4)` (`Adm942RankForcing.lowPort_mod_four`)
  and oddness of `J` (forced by `q = βJ + 1`).

The port-generic helpers (`ι_tsub`, `mod4_val`, `mod4_of_dvd`,
`mod_four_of_mod4`, `four_dvd_exp`) are reused from `ArithmeticThirteenOuter`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option Elab.async false
noncomputable section
namespace Adm942ThirteenOuter
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open Adm942CarrierRadix Adm942Ports ModelDifferenceRing
open DiscreteOrderedRingFacts ModelArithmetic
open ArithmeticThirteenOuter (ι_tsub mod4_val mod4_of_dvd mod_four_of_mod4 four_dvd_exp)
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The spatial shift exceeds the base at every positive zero. -/
theorem base_lt_shift (u : Fin 14 → V) (h : PositiveZero u) : q u < u 8 := by
  obtain ⟨L, hL, hq, _, hw, _, _⟩ := (current_radix u h.1 h.2).2
  have h3 := Adm942HalfBinomial.three_h_lt_rank u h.1 _ hq
  rw [hq, hw]
  apply exp_monotone.mpr
  set WL := (Adm942MaskData.width : V) * L
  apply lt_tsub_iff_left.mpr
  calc WL + WL ≤ WL + WL + WL := le_self_add
    _ = 3 * WL := by ring
    _ < 3 * WL + 1 := lt_add_of_pos_right _ _root_.zero_lt_one
    _ ≤ rank u := h3

/-- The window coordinate `C = q - F - α` is positive, so `F < q` and `α < q - F`. -/
theorem window_positive (u : Fin 14 → V) (h : PositiveZero u) :
    u 2 < q u - u 1 ∧ u 1 < q u := by
  obtain ⟨N, _, hwin⟩ := Adm942WindowZero.window_of_positive_zero u h
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
  have hWL : 2 ≤ (Adm942MaskData.width : V) * L := by
    have hW : (2 : V) ≤ (Adm942MaskData.width : V) := (current_width (V := V)).2
    calc (2 : V) = 2 * 1 := (mul_one 2).symm
      _ ≤ (Adm942MaskData.width : V) * L :=
        mul_le_mul hW (pos_iff_one_le.mp hL) (by simp) (by simp)
  have hq0 : mod4 (ι (q u)) = 0 := mod4_of_dvd (by rw [hqL]; exact four_dvd_exp hWL)
  -- the window origin: C ≡ 1 (mod 4)
  obtain ⟨N, _, hwin⟩ := Adm942WindowZero.window_of_positive_zero u h
  have horig := hwin.origin
  rw [ArithmeticWindowDigits.dig_zero_index] at horig
  have hC : q u - u 1 - u 2 =
      4*((Exp.exp (45:V)) * ((q u - u 1 - u 2) / Exp.exp 47)) + (1 : ℕ) := by
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
  have hMC : mod4 (ι (Adm942MaskData.lowPort : V)) = 2 := by
    have hlp := Adm942RankForcing.lowPort_mod_four (V := V)
    generalize (Adm942MaskData.lowPort : V) = Lp at hlp ⊢
    have h0 := (div_add_mod Lp 4).symm
    rw [hlp] at h0
    have hx : Lp = 4 * (Lp / 4) + ((2 : ℕ) : V) := by exact_mod_cast h0
    have := mod4_val hx
    exact_mod_cast this
  -- the base factor: beta * J = q - 1
  have hq1 : 1 ≤ q u := by
    show 1 ≤ (Adm942MaskData.beta:V) * u 0 + 1; exact le_add_self
  have hbJ : mod4 (ι ((Adm942MaskData.beta:V) * u 0)) = -1 := by
    have : (Adm942MaskData.beta:V) * u 0 = q u - 1 := by
      rw [show q u = (Adm942MaskData.beta:V) * u 0 + 1 from rfl, add_tsub_cancel_right]
    rw [this, ι_tsub hq1, map_sub, hq0, map_one, map_one, _root_.zero_sub]
  have hJodd : 2 * mod4 (ι (u 0)) = 2 := by
    rw [map_mul, map_mul] at hbJ
    revert hbJ
    generalize mod4 (ι (Adm942MaskData.beta : V)) = a
    generalize mod4 (ι (u 0)) = j
    revert a j; decide
  -- the rank
  have hq2 : 1 ≤ q u ^ 2 := one_le_pow₀ hq1
  have hrank : ι (rank u) =
      ((ι (q u) - 1) * (ι (q u) - ι (u 1)) + ι (u 2)) * (ι (q u) ^ 2 - 1) +
      (ι (Adm942MaskData.lowPort : V) +
        ι (q u) * ι (((Adm942MaskData.highPort + Adm942MaskData.beta : ℕ) : V))) * ι (u 0) := by
    unfold rank
    rw [map_add, map_mul, map_mul, map_add, map_mul, ι_tsub hq1, ι_tsub hFlt.le, ι_tsub hq2,
      map_one, map_pow, map_add, map_mul]
  apply mod_four_of_mod4 (by norm_num)
  rw [hrank]
  generalize ι (((Adm942MaskData.highPort + Adm942MaskData.beta : ℕ) : V)) = Hp
  simp only [map_add, map_mul, map_sub, map_pow, map_one, hq0, hMC]
  have hFα : mod4 (ι (u 1)) + mod4 (ι (u 2)) = -1 := by linear_combination -hC1
  push_cast
  linear_combination -hFα + hJodd

end Adm942ThirteenOuter

#print axioms Adm942ThirteenOuter.base_lt_shift
#print axioms Adm942ThirteenOuter.window_positive
#print axioms Adm942ThirteenOuter.rank_mod_four
