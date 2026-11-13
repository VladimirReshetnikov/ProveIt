import DiophantineConsistency.P138.P138Ratio
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.BFS943.Direct80ProjectionProduct

/-! # The signed projector: `σ X = 2^R`

132-lowops §5, third paragraph, with the audit's negative-base fix (p138risk/AUDIT.md §1). At a
zero, with `σ = sign c`, `X' = σX`, `c' = σc = |c|`:

* the main congruence `d = 2^R + a|c| + H z` with `d² = Dm`, for **either** sign of `A`
  (`signed_main`): `A > 0` is `ArithmeticPellPowerRecovery.projection_quotient` at base
  `a = A − 2`; `A < 0` uses `d := −χ_B(R)` and the odd-index congruence `neg_projection_odd`
  (`χ_b(2u+1) + 2^(2u+1) ≡ (b+4) ψ_b(2u+1) (mod 4b+13)`, `b = |A| − 2`, so `4b + 13 = −H`);
* `H ∣ Kq⁵` (`P138Rank.Folded.hHK`, `Kq = X'X' + 2aX'c' − 1`) and five applications of
  `Direct80ProjectionProduct.entire_product` give `H ∣ Π⁵`, `Π = (X' − 2^R)(2^R X' + 1)`
  (`fifth_power`);
* `|Π|⁵ ≤ (x (2^R + 1))^10 ≤ x (x − 3)^t < |H|` (`height_power`, `P138Ratio.H_large`), so
  `Π = 0`; the second factor is odd, hence `X' = 2^R` (`projector`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Projector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold P138Rank P138FirstIndex P138Ratio
open ArithmeticPellRecurrence ArithmeticPow

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The negative main base -/

/-- The parity-tagged negative-base congruences modulo `M = 4b + 13`: at even time
`χ_b(n) ≡ 2^n + (b+4) ψ_b(n)`, at odd time `χ_b(n) + 2^n ≡ (b+4) ψ_b(n)` (nonnegative
quotients). This is `projection_quotient` at the reflected base `−(b+2)`. -/
theorem neg_projection (b n : V) :
    (∃ z1 z2 q : V, n = 2 * q ∧
      xcoord n b + (4 * b + 13) * z1 = Exp.exp n + (b + 4) * ycoord n b + (4 * b + 13) * z2) ∨
    (∃ z1 z2 q : V, n = 2 * q + 1 ∧
      xcoord n b + Exp.exp n + (4 * b + 13) * z1 = (b + 4) * ycoord n b + (4 * b + 13) * z2) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact Or.inl ⟨0, 0, 0, by simp, by simp⟩
  case succ n ih =>
    rcases ih with ⟨z1, z2, q, hq, h⟩ | ⟨z1, z2, q, hq, h⟩
    · refine Or.inr ⟨2 * z2 + ycoord n b, 2 * z1, q, by rw [hq], ?_⟩
      rw [x_succ, y_succ, exp_succ]
      unfold delta
      apply ι_injective
      have h' := congrArg (ι (V := V)) h
      simp only [map_add, map_mul, map_ofNat, map_one] at h' ⊢
      linear_combination (-2 : DiffRing V) * h'
    · refine Or.inl ⟨ycoord n b + 2 * z2, 2 * z1, q + 1, by rw [hq]; ring, ?_⟩
      rw [x_succ, y_succ, exp_succ]
      unfold delta
      apply ι_injective
      have h' := congrArg (ι (V := V)) h
      simp only [map_add, map_mul, map_ofNat, map_one] at h' ⊢
      linear_combination (-2 : DiffRing V) * h'

/-- `χ_b(2u+1) + 2^(2u+1) ≡ (b+4) ψ_b(2u+1) (mod 4b+13)`, with nonnegative quotients. -/
theorem neg_projection_odd (b u : V) : ∃ z1 z2 : V,
    xcoord (2 * u + 1) b + Exp.exp (2 * u + 1) + (4 * b + 13) * z1 =
      (b + 4) * ycoord (2 * u + 1) b + (4 * b + 13) * z2 := by
  rcases neg_projection b (2 * u + 1) with ⟨_, _, q, hq, _⟩ | ⟨z1, z2, _, _, h⟩
  · exfalso
    have h' := congrArg (ι (V := V)) hq
    simp only [map_add, map_mul, map_ofNat, map_one] at h'
    exact P138Bootstrap.odd_ne_zero' (ι u - ι q) (by linear_combination h')
  · exact ⟨z1, z2, h⟩

/-! ## The product projector, five times -/

section Ring
variable {R : Type*} [CommRing R]

theorem product_step (a c d t X z b : R) (hd : d = t + a * c + (4 * a + 3) * z)
    (hnorm : d * d = 1 + (a * a + (4 * a + 3)) * c * c)
    (h : (4 * a + 3) ∣ b * (X * X + 2 * a * X * c - 1)) :
    (4 * a + 3) ∣ b * ((X - t) * (t * X + 1)) := by
  have hdiv : (4 * a + 3) ∣ b * ((4 * a + 3) * X * c - 2 * (X * X + 2 * a * X * c - 1)) := by
    rw [show b * ((4 * a + 3) * X * c - 2 * (X * X + 2 * a * X * c - 1)) =
      (4 * a + 3) * (b * X * c) - 2 * (b * (X * X + 2 * a * X * c - 1)) by ring]
    exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right h 2)
  have := Direct80ProjectionProduct.entire_product a c d t X b z hd hnorm hdiv
  rwa [mul_assoc] at this

theorem fifth_power (a c d t X z : R) (hd : d = t + a * c + (4 * a + 3) * z)
    (hnorm : d * d = 1 + (a * a + (4 * a + 3)) * c * c)
    (hK : (4 * a + 3) ∣ (X * X + 2 * a * X * c - 1) ^ 5) :
    (4 * a + 3) ∣ ((X - t) * (t * X + 1)) ^ 5 := by
  set K := X * X + 2 * a * X * c - 1 with hKdef
  set P := (X - t) * (t * X + 1) with hPdef
  have s1 := product_step a c d t X z (K ^ 4) hd hnorm (by rw [← pow_succ]; exact hK)
  have s2 := product_step a c d t X z (K ^ 3 * P) hd hnorm
    (by rw [show K ^ 3 * P * K = K ^ 4 * P by ring]; exact s1)
  have s3 := product_step a c d t X z (K ^ 2 * P ^ 2) hd hnorm
    (by rw [show K ^ 2 * P ^ 2 * K = K ^ 3 * P * P by ring]; exact s2)
  have s4 := product_step a c d t X z (K * P ^ 3) hd hnorm
    (by rw [show K * P ^ 3 * K = K ^ 2 * P ^ 2 * P by ring]; exact s3)
  have s5 := product_step a c d t X z (P ^ 4) hd hnorm
    (by rw [show P ^ 4 * K = K * P ^ 3 * P by ring]; exact s4)
  rwa [show P ^ 4 * P = P ^ 5 by ring] at s5

end Ring

/-! ## The height of the product -/

theorem exp_pow_nat (m : V) (n : ℕ) : (Exp.exp m) ^ n = Exp.exp ((n : V) * m) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, exp_add]

theorem exp_nat (n : ℕ) : Exp.exp (n : V) = 2 ^ n := by
  have := exp_pow_nat (V := V) 1 n
  rw [exp_one, mul_one] at this; exact this.symm

theorem power_nat (z : V) (n : ℕ) : power z (n : V) = z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, power_succ, ih, pow_succ, mul_comm]

/-- `(x (2^(2t+1) + 1))^10 ≤ x (x − 3)^t` for `x ≥ 2^66`, `t ≥ 14`. -/
theorem height_power (xn t : V) (hx : Exp.exp (66 : V) ≤ xn) (ht : 14 ≤ t) :
    (xn * (Exp.exp (2 * t + 1) + 1)) ^ 10 ≤ xn * power (xn - 3) t := by
  have e66 : Exp.exp (66 : V) = 8 * Exp.exp 63 := by
    rw [show (66 : V) = 63 + 1 + 1 + 1 by norm_num, exp_succ, exp_succ, exp_succ]; ring
  have h63 : (1 : V) ≤ Exp.exp 63 := one_le_exp _
  have hx3 : (3 : V) ≤ xn := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr hx; have h1 := ι_le_ι.mpr h63
    rw [e66, map_mul, map_ofNat] at this; rw [map_one] at h1; rw [map_ofNat]; linarith
  have hsub : (ι (xn - 3) : DiffRing V) = ι xn - 3 := by rw [ι_tsub' hx3, map_ofNat]
  -- `xn ≤ 2 (xn − 3)` and `2^63 ≤ xn − 3`
  have hx2 : xn ≤ 2 * (xn - 3) := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr hx; have h1 := ι_le_ι.mpr h63
    rw [e66, map_mul, map_ofNat] at this; rw [map_one] at h1
    rw [map_mul, map_ofNat, hsub]; linarith
  have hx63 : Exp.exp 63 ≤ xn - 3 := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr hx; have h1 := ι_le_ι.mpr h63
    rw [e66, map_mul, map_ofNat] at this; rw [map_one] at h1
    rw [hsub]; linarith
  -- `t = s + 9`, `s ≥ 5`
  have h9 : (9 : V) ≤ t := le_trans (by norm_num) ht
  set s := t - 9 with hs
  have hts : t = s + 9 := (tsub_add_cancel_of_le h9).symm
  have hs5 : (5 : V) ≤ s := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr ht
    rw [hs, ι_tsub' h9]; simp only [map_ofNat] at this ⊢; linarith
  -- exponent bookkeeping
  have hT : Exp.exp (2 * t + 1) + 1 ≤ Exp.exp (2 * t + 2) := by
    have e : Exp.exp (2 * t + 2) = 2 * Exp.exp (2 * t + 1) := by
      rw [show 2 * t + 2 = (2 * t + 1) + 1 by ring]; exact exp_succ _
    rw [e]
    calc Exp.exp (2 * t + 1) + 1 ≤ Exp.exp (2 * t + 1) + Exp.exp (2 * t + 1) :=
          add_le_add le_rfl (one_le_exp (2 * t + 1))
      _ = 2 * Exp.exp (2 * t + 1) := (two_mul _).symm
  have hE10 : (Exp.exp (2 * t + 2)) ^ 10 = Exp.exp (20 * t + 20) := by
    rw [exp_pow_nat]; congr 1; push_cast; ring
  have hle_exp : 20 * t + 29 ≤ 63 * s := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr hs5
    rw [hts]; simp only [map_add, map_mul, map_ofNat] at this ⊢; linarith
  have hpow63 : Exp.exp (63 * s) ≤ power (xn - 3) s := by
    rw [← power_two, ← power_iterate, power_two]
    exact power_mono_base _ _ s hx63
  have h2x : xn ^ 9 ≤ Exp.exp 9 * (xn - 3) ^ 9 := by
    have h1 : xn ^ 9 ≤ (2 * (xn - 3)) ^ 9 := pow_le_pow_left₀ (by simp) hx2 9
    rw [mul_pow] at h1
    have e9 : (2 : V) ^ 9 = Exp.exp 9 := by
      have := exp_nat (V := V) 9; rw [Nat.cast_ofNat] at this; exact this.symm
    rwa [e9] at h1
  have hpow9 : (xn - 3) ^ 9 = power (xn - 3) 9 := by
    have := power_nat (xn - 3) 9; rw [Nat.cast_ofNat] at this; exact this.symm
  calc (xn * (Exp.exp (2 * t + 1) + 1)) ^ 10
      = xn ^ 10 * (Exp.exp (2 * t + 1) + 1) ^ 10 := by rw [mul_pow]
    _ ≤ xn ^ 10 * (Exp.exp (2 * t + 2)) ^ 10 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by simp) hT 10) (by simp)
    _ = xn * (xn ^ 9 * Exp.exp (20 * t + 20)) := by rw [hE10]; ring
    _ ≤ xn * (Exp.exp 9 * (xn - 3) ^ 9 * Exp.exp (20 * t + 20)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2x (by simp)) (by simp)
    _ = xn * ((xn - 3) ^ 9 * Exp.exp (20 * t + 29)) := by
        rw [show 20 * t + 29 = (20 * t + 20) + 9 by ring, exp_add (20 * t + 20) 9]; ring
    _ ≤ xn * ((xn - 3) ^ 9 * Exp.exp (63 * s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (exp_monotone_le.mpr hle_exp) (by simp)) (by simp)
    _ ≤ xn * (power (xn - 3) 9 * power (xn - 3) s) := by
        rw [hpow9]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow63 (by simp)) (by simp)
    _ = xn * power (xn - 3) t := by rw [← power_add, hts, add_comm]

/-! ## At a zero -/

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK p x κ

/-- **The main congruence, either sign of `A`.** -/
theorem signed_main (Fd : Folded p x κ) :
    ∃ d z : DiffRing V, d * d = (𝓡).Dm ∧
      d = ι (Exp.exp Fd.Rn) + (𝓡).a * ι Fd.cn + (4 * (𝓡).a + 3) * z := by
  obtain ⟨u, hu⟩ := P72ConvArith.odd_of_mod_two Fd.hodd
  set b := Fd.Bn - 2 with hb
  have hbB : (ι b : DiffRing V) = ι Fd.Bn - 2 := by
    rw [hb, ι_tsub' (le_trans (by norm_num) Fd.hB3), map_ofNat]
  have ha : (𝓡).a = (𝓡).A - 2 := by rw [A_eq]; ring
  rcases eq_or_eq_neg_abs (𝓡).A with hA | hA <;> rw [Fd.hBn] at hA
  · -- `A > 0`: base `a`
    obtain ⟨z, hz⟩ := ArithmeticPellPowerRecovery.projection_quotient b Fd.Rn
    refine ⟨ι (xcoord Fd.Rn b), ι z, Fd.hDm.symm, ?_⟩
    have := congrArg (ι (V := V)) hz
    simp only [map_add, map_mul, map_ofNat] at this
    rw [this, Fd.hc, ha, hA, ← hbB]
  · -- `A < 0`: `d = −χ`
    obtain ⟨z1, z2, hz⟩ := neg_projection_odd b u
    refine ⟨-ι (xcoord Fd.Rn b), ι z2 - ι z1, by rw [neg_mul_neg]; exact Fd.hDm.symm, ?_⟩
    have := congrArg (ι (V := V)) hz
    simp only [map_add, map_mul, map_ofNat] at this
    rw [← hu] at this
    rw [ha, hA, Fd.hc]
    have hB' : (ι Fd.Bn : DiffRing V) = ι b + 2 := by rw [hbB]; ring
    rw [hB']
    linear_combination -this

theorem eq_zero_of_dvd_lt {H D : DiffRing V} (h : H ∣ D) (hD : |D| < |H|) : D = 0 := by
  obtain ⟨w, rfl⟩ := h
  by_contra hne
  have hw : w ≠ 0 := by intro h0; apply hne; rw [h0, mul_zero]
  have h1 : 1 ≤ |w| := one_le_abs hw
  rw [abs_mul] at hD
  have : |H| * 1 ≤ |H| * |w| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  linarith

set_option maxHeartbeats 2000000 in
/-- **The signed projector.** `σ X = 2^R` with `x 8 = σ |c|`. -/
theorem projector (hp : PortFacts p) (Fd : Folded p x κ) (Fi : FirstIndex p x κ Fd) :
    ∃ σ : DiffRing V, (σ = 1 ∨ σ = -1) ∧ x 8 = σ * ι Fd.cn ∧
      σ * (𝓡).X = ι (Exp.exp Fd.Rn) := by
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two Fd.hodd
  obtain ⟨xn, hxn⟩ := abs_eq_ι (𝓡).X
  obtain ⟨d, z, hdd, hd⟩ := signed_main p x κ Fd
  have hHK := Fd.hHK
  have hlarge := H_large p x κ hp Fd Fi t xn ht hxn
  -- the sign of `c`
  obtain ⟨σ, hσ, hcσ⟩ : ∃ σ : DiffRing V, (σ = 1 ∨ σ = -1) ∧ x 8 = σ * ι Fd.cn := by
    rcases eq_or_eq_neg_abs (x 8) with h | h <;> rw [Fd.hcn] at h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> ring
  refine ⟨σ, hσ, hcσ, ?_⟩
  set T : DiffRing V := ι (Exp.exp Fd.Rn) with hT
  set X' := σ * (𝓡).X with hX'
  have hnorm : d * d = 1 + ((𝓡).a * (𝓡).a + (4 * (𝓡).a + 3)) * ι Fd.cn * ι Fd.cn := by
    rw [hdd, Dm_eq, Delta_def, H_def, hcσ]
    linear_combination (((𝓡).a * (𝓡).a + (4 * (𝓡).a + 3)) * ι Fd.cn * ι Fd.cn) * hσσ
  have hK : (4 * (𝓡).a + 3) ∣ (X' * X' + 2 * (𝓡).a * X' * ι Fd.cn - 1) ^ 5 := by
    have e : X' * X' + 2 * (𝓡).a * X' * ι Fd.cn - 1 = Kq p x κ := by
      unfold Kq; rw [hX', hcσ]
      linear_combination ((𝓡).X * (𝓡).X) * hσσ
    rw [e, ← H_def]; exact hHK
  have h5 := fifth_power (𝓡).a (ι Fd.cn) d T X' z hd hnorm hK
  rw [← H_def] at h5
  -- the height
  have hX66 : Exp.exp (66 : V) ≤ xn := by
    apply ι_le_ι.mp
    rw [← hxn]
    have := abs_X_ge p x κ hp
    have e : (ι (Exp.exp (66 : V)) : DiffRing V) = 2 ^ 66 := by
      have h := exp_nat (V := V) 66
      rw [Nat.cast_ofNat] at h
      rw [h, map_pow, map_ofNat]
    rw [e]; exact this
  have ht14 : (14 : V) ≤ t := by
    apply ι_le_ι.mp
    have h4 : (4080 : DiffRing V) ≤ ι Fd.Rn := by
      have := R_ge p x κ hp (signs_of_budget p x κ hp Fd.hbudget); rwa [Fd.hR] at this
    rw [ht] at h4; simp only [map_add, map_mul, map_ofNat, map_one] at h4; rw [map_ofNat]
    linarith
  have hheight := height_power xn t hX66 ht14
  have hT1 : (1 : DiffRing V) ≤ T := by rw [hT, ← map_one ι]; exact ι_le_ι.mpr (one_le_exp _)
  have hX'abs : |X'| = ι xn := by
    rw [hX', abs_mul, hxn]; rcases hσ with h | h <;> rw [h] <;> simp
  have hxn1 : (1 : DiffRing V) ≤ ι xn := by
    rw [← hxn]; have := abs_X_ge p x κ hp
    have : (1 : DiffRing V) ≤ 2 ^ 66 := one_le_pow₀ (by norm_num); linarith
  have hP : |(X' - T) * (T * X' + 1)| ≤ (ι xn * (T + 1)) ^ 2 := by
    rw [abs_mul]
    have h1 : |X' - T| ≤ ι xn * (T + 1) := by
      have := abs_add_le X' (-T)
      rw [← sub_eq_add_neg, abs_neg, hX'abs,
        abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T)] at this
      nlinarith
    have h2 : |T * X' + 1| ≤ ι xn * (T + 1) := by
      have := abs_add_le (T * X') 1
      rw [abs_mul, hX'abs, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T), abs_one] at this
      nlinarith
    rw [sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (ι_nonneg _) (by linarith))
  have hP5 : |((X' - T) * (T * X' + 1)) ^ 5| < |(𝓡).H| := by
    rw [abs_pow]
    have h1 : |(X' - T) * (T * X' + 1)| ^ 5 ≤ ((ι xn * (T + 1)) ^ 2) ^ 5 :=
      pow_le_pow_left₀ (abs_nonneg _) hP 5
    have h2 : ((ι xn * (T + 1)) ^ 2) ^ 5 = ι ((xn * (Exp.exp Fd.Rn + 1)) ^ 10) := by
      rw [hT]; simp only [map_pow, map_mul, map_add, map_one]; ring
    have h3 : (ι ((xn * (Exp.exp Fd.Rn + 1)) ^ 10) : DiffRing V) ≤ ι (xn * power (xn - 3) t) := by
      apply ι_le_ι.mpr; rw [ht]; exact hheight
    linarith
  have h0 := eq_zero_of_dvd_lt h5 hP5
  rcases mul_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp h0) with h | h
  · linear_combination h
  · exfalso
    have hT2 : (2 : DiffRing V) ≤ T := by
      have h1 : (1 : V) ≤ Fd.Rn := pos_iff_one_le.mp Fd.hRpos
      have h2 : (2 : V) ≤ Exp.exp Fd.Rn := by
        calc (2 : V) = Exp.exp 1 := exp_one.symm
          _ ≤ Exp.exp Fd.Rn := exp_monotone_le.mpr h1
      have h3 := ι_le_ι.mpr h2
      rw [map_ofNat] at h3
      rw [hT]; exact h3
    have hX'1 : 1 ≤ |X'| := by rw [hX'abs]; exact hxn1
    have : |T * X'| = 1 := by
      rw [show T * X' = -1 by linear_combination h, abs_neg, abs_one]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T)] at this
    nlinarith

end Regs

#print axioms neg_projection
#print axioms neg_projection_odd
#print axioms fifth_power
#print axioms height_power
#print axioms signed_main
#print axioms projector

end DiophantineConsistency.P138Projector
