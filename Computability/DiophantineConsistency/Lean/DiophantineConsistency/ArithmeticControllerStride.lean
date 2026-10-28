import DiophantineConsistency.ArithmeticControllerData

/-! **K5d — derived stride and multiplier** (construction spec §7 K4), in every
model of IΣ1.

From the calibrated rank congruence `R ≡ d·s (mod d·N)` (★) with `0 < s < N`
and `2·d·N < R` (rank forcing, K4), the stride `t = R/d − N` and the
multiplier `w = 2^(R − d·N)` satisfy

* `d·t + d·N = R`, `N < t`, `t mod N = s`;
* `w · 2^(d·N) = 2^R` (the forced product `w·q = X`);
* `w ≡ 2^(d·s) (mod 2^(d·N) − 1)` — exactly the hypothesis `hW` of
  `ArithmeticPacking.packing_transport` (with `B^s = 2^(d·s)`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticControllerStride
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticControllerData

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Derived stride and multiplier.** -/
theorem stride (d N s R : V) (hd : 0 < d) (hs0 : 0 < s) (hsN : s < N)
    (hR : R % (d * N) = (d * s) % (d * N)) (hbig : 2 * (d * N) < R) :
    d * (R / d - N) + d * N = R ∧ N < R / d - N ∧ (R / d - N) % N = s ∧
      Exp.exp (R - d * N) * Exp.exp (d * N) = Exp.exp R ∧
      Exp.exp (R - d * N) % (Exp.exp (d * N) - 1) = Exp.exp (d * s) % (Exp.exp (d * N) - 1) := by
  have hN : 0 < N := lt_of_le_of_lt (Arithmetic.zero_le s) hsN
  have hM : 0 < d * N := mul_pos hd hN
  have hds : d * s < d * N := mul_lt_mul_of_pos_left hsN hd
  rw [mod_eq_self_of_lt hds] at hR
  have hRd : d * N * (R / (d * N)) + d * s = R := by
    have := div_add_mod R (d * N); rwa [hR] at this
  set q := R / (d * N)
  -- q ≥ 2
  have hq2 : 2 ≤ q := by
    by_contra hc
    have hq1 : q ≤ 1 := by
      have : q < 1 + 1 := by rw [one_add_one_eq_two]; exact lt_of_not_ge hc
      exact le_iff_lt_succ.mpr this
    have : R < 2 * (d * N) := by
      calc R = d * N * q + d * s := hRd.symm
        _ < d * N * 1 + d * N := add_lt_add_of_le_of_lt
            (mul_le_mul_of_nonneg_left hq1 (Arithmetic.zero_le _)) hds
        _ = 2 * (d * N) := by ring
    exact absurd hbig (not_lt.mpr this.le)
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 + 1 := ⟨q - 2, by
    rw [add_assoc, one_add_one_eq_two, tsub_add_cancel_of_le hq2]⟩
  have hRform : R = d * (N * (r + 1) + s) + d * N := by
    rw [← hRd, hr]; ring
  have hdiv : R / d - N = N * (r + 1) + s := by
    rw [hRform, show d * (N * (r + 1) + s) + d * N = d * (N * (r + 1) + s + N) by ring,
      div_mul_right _ hd, add_tsub_cancel_right]
  have hRu : R - d * N = d * (N * (r + 1) + s) := by
    rw [hRform, add_tsub_cancel_right]
  have hle : d * N ≤ R := le_of_lt (lt_of_le_of_lt (le_mul_of_one_le_left (Arithmetic.zero_le _)
    (by norm_num : (1 : V) ≤ 2)) hbig)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdiv, hRform]
  · rw [hdiv]
    calc N < N + s := lt_add_of_pos_right N hs0
      _ ≤ N * (r + 1) + s := add_le_add (le_mul_of_one_le_right (Arithmetic.zero_le _)
          (le_add_of_nonneg_left (Arithmetic.zero_le r))) le_rfl
  · rw [hdiv, add_comm, mod_add_mul' _ _ hN, mod_eq_self_of_lt hsN]
  · rw [← exp_add, tsub_add_cancel_of_le hle]
  · have hq0 : (1 : V) ≤ Exp.exp (d * N) := one_le_exp _
    have hq1 : (0 : V) < Exp.exp (d * N) - 1 := tsub_pos_of_lt (one_lt_exp hM)
    obtain ⟨t', ht'⟩ := power_one_add_mul (Exp.exp (d * N) - 1) (r + 1)
    rw [add_tsub_cancel_of_le hq0, ← power_two, power_iterate] at ht'
    simp only [power_two] at ht'
    rw [hRu, mul_add, exp_add, show d * (N * (r + 1)) = d * N * (r + 1) by ring, ht',
      show (1 + (Exp.exp (d * N) - 1) * t') * Exp.exp (d * s) =
        Exp.exp (d * s) + (Exp.exp (d * N) - 1) * (t' * Exp.exp (d * s)) by ring,
      mod_add_mul' _ _ hq1]

end DiophantineConsistency.ArithmeticControllerStride
