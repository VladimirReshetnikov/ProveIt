import DiophantineConsistency.LinCof.LCRatio
import DiophantineConsistency.P138.P138Projector

/-! # The signed projector for the linear cofactor: `σ X = 2^R`

The linear-cofactor form of `P138Projector.projector`. At a zero, with `σ = sign c`,
`X' = σX`, `c' = σc = |c|`:

* the main congruence `d = 2^R + a|c| + H z` with `d² = Dm`, for either sign of `A`
  (`signed_main`; the negative base uses `P138Projector.neg_projection_odd`);
* the carrier gives `H ∣ q¹⁵ Kq⁵` (`LCCarrier.H_dvd_q15_Kq5`; the factor `q¹⁵` is new, since
  the scale `Y` is free and `M = 2q³` is only cleared later), and five applications of
  `P138Projector.product_step` give `H ∣ q¹⁵ Π⁵`, `Π = (X' − 2^R)(2^R X' + 1)`
  (`fifth_power_mul`);
* `|q|¹⁵ |Π|⁵ ≤ x¹⁵ (x (2^R + 1))^10 ≤ x (x − 3)^t < |H|` (`height_power15`,
  `LCRatio.H_large`), so `Π = 0`; the second factor is odd, hence `X' = 2^R` (`projector`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCProjector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCSquares LCBudget LCAdjacent LCWindow
  LCCarrier LCEarlyFold LCRank LCFirstIndex LCRatio
open ArithmeticPellRecurrence ArithmeticPow
open ZRowsCoprimeSquares (abs_eq_ι eq_or_eq_neg_abs)
open P138EarlyFold (ι_tsub')
open P138Projector (neg_projection_odd product_step exp_pow_nat exp_nat power_nat
  eq_zero_of_dvd_lt)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The product projector, five times, with a multiplier -/

section Ring
variable {R : Type*} [CommRing R]

theorem fifth_power_mul (a c d t X z g : R) (hd : d = t + a * c + (4 * a + 3) * z)
    (hnorm : d * d = 1 + (a * a + (4 * a + 3)) * c * c)
    (hK : (4 * a + 3) ∣ g * (X * X + 2 * a * X * c - 1) ^ 5) :
    (4 * a + 3) ∣ g * ((X - t) * (t * X + 1)) ^ 5 := by
  obtain ⟨K, hKdef⟩ : ∃ K : R, K = X * X + 2 * a * X * c - 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : R, P = (X - t) * (t * X + 1) := ⟨_, rfl⟩
  rw [← hKdef] at hK
  rw [← hPdef]
  have step : ∀ b : R, (4 * a + 3) ∣ b * K → (4 * a + 3) ∣ b * P := by
    intro b hb
    rw [hPdef]
    exact product_step a c d t X z b hd hnorm (by rw [← hKdef]; exact hb)
  have s1 := step (g * K ^ 4) (by rw [show g * K ^ 4 * K = g * K ^ 5 by ring]; exact hK)
  have s2 := step (g * K ^ 3 * P)
    (by rw [show g * K ^ 3 * P * K = g * K ^ 4 * P by ring]; exact s1)
  have s3 := step (g * K ^ 2 * P ^ 2)
    (by rw [show g * K ^ 2 * P ^ 2 * K = g * K ^ 3 * P * P by ring]; exact s2)
  have s4 := step (g * K * P ^ 3)
    (by rw [show g * K * P ^ 3 * K = g * K ^ 2 * P ^ 2 * P by ring]; exact s3)
  have s5 := step (g * P ^ 4)
    (by rw [show g * P ^ 4 * K = g * K * P ^ 3 * P by ring]; exact s4)
  rwa [show g * P ^ 4 * P = g * P ^ 5 by ring] at s5

end Ring

/-! ## The height of the product -/

set_option maxHeartbeats 1000000 in
/-- `(x (2^(2t+1) + 1))^10 x^15 ≤ x (x − 3)^t` for `x ≥ 2^66`, `t ≥ 40`. -/
theorem height_power15 (xn t : V) (hx : Exp.exp (66 : V) ≤ xn) (ht : 40 ≤ t) :
    (xn * (Exp.exp (2 * t + 1) + 1)) ^ 10 * xn ^ 15 ≤ xn * power (xn - 3) t := by
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
  -- `t = s + 24`, `s ≥ 16`
  have h24 : (24 : V) ≤ t := le_trans (by norm_num) ht
  set s := t - 24 with hs
  have hts : t = s + 24 := (tsub_add_cancel_of_le h24).symm
  have hs16 : (16 : V) ≤ s := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr ht
    rw [hs, ι_tsub' h24]; simp only [map_ofNat] at this ⊢; linarith
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
  have hle_exp : 20 * t + 44 ≤ 63 * s := by
    apply ι_le_ι.mp
    have := ι_le_ι.mpr hs16
    rw [hts]; simp only [map_add, map_mul, map_ofNat] at this ⊢; linarith
  have hpow63 : Exp.exp (63 * s) ≤ power (xn - 3) s := by
    rw [← power_two, ← power_iterate, power_two]
    exact power_mono_base _ _ s hx63
  have h2x : xn ^ 24 ≤ Exp.exp 24 * (xn - 3) ^ 24 := by
    have h1 : xn ^ 24 ≤ (2 * (xn - 3)) ^ 24 := pow_le_pow_left₀ (by simp) hx2 24
    rw [mul_pow] at h1
    have e24 : (2 : V) ^ 24 = Exp.exp 24 := by
      have := exp_nat (V := V) 24; rw [Nat.cast_ofNat] at this; exact this.symm
    rwa [e24] at h1
  have hpow24 : (xn - 3) ^ 24 = power (xn - 3) 24 := by
    have := power_nat (xn - 3) 24; rw [Nat.cast_ofNat] at this; exact this.symm
  calc (xn * (Exp.exp (2 * t + 1) + 1)) ^ 10 * xn ^ 15
      = xn ^ 25 * (Exp.exp (2 * t + 1) + 1) ^ 10 := by rw [mul_pow]; ring
    _ ≤ xn ^ 25 * (Exp.exp (2 * t + 2)) ^ 10 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by simp) hT 10) (by simp)
    _ = xn * (xn ^ 24 * Exp.exp (20 * t + 20)) := by rw [hE10]; ring
    _ ≤ xn * (Exp.exp 24 * (xn - 3) ^ 24 * Exp.exp (20 * t + 20)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2x (by simp)) (by simp)
    _ = xn * ((xn - 3) ^ 24 * Exp.exp (20 * t + 44)) := by
        rw [show 20 * t + 44 = (20 * t + 20) + 24 by ring, exp_add (20 * t + 20) 24]; ring
    _ ≤ xn * ((xn - 3) ^ 24 * Exp.exp (63 * s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (exp_monotone_le.mpr hle_exp) (by simp)) (by simp)
    _ ≤ xn * (power (xn - 3) 24 * power (xn - 3) s) := by
        rw [hpow24]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow63 (by simp)) (by simp)
    _ = xn * power (xn - 3) t := by rw [← power_add, hts, add_comm]

/-! ## At a zero -/

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **The main congruence, either sign of `A`.** -/
theorem signed_main (E : EarlyFold p x κ ω Λ ψ wt) (M : MainIndex p x κ ω Λ ψ wt E) :
    ∃ d z : DiffRing V, d * d = (𝓡).Dm ∧
      d = ι (Exp.exp M.Rn) + (𝓡).a * ι E.cn + (4 * (𝓡).a + 3) * z := by
  obtain ⟨u, hu⟩ := P72ConvArith.odd_of_mod_two M.hodd
  set b := E.Bn - 2 with hb
  have hbB : (ι b : DiffRing V) = ι E.Bn - 2 := by
    rw [hb, ι_tsub' (le_trans (by norm_num) E.hB3), map_ofNat]
  have ha : (𝓡).a = (𝓡).A - 2 := by rw [A_eq]; ring
  rcases eq_or_eq_neg_abs (𝓡).A with hA | hA <;> rw [E.hBn] at hA
  · -- `A > 0`: base `a`
    obtain ⟨z, hz⟩ := ArithmeticPellPowerRecovery.projection_quotient b M.Rn
    refine ⟨ι (xcoord M.Rn b), ι z, M.hDm.symm, ?_⟩
    have := congrArg (ι (V := V)) hz
    simp only [map_add, map_mul, map_ofNat] at this
    rw [this, M.hc, ha, hA, ← hbB]
  · -- `A < 0`: `d = −χ`
    obtain ⟨z1, z2, hz⟩ := neg_projection_odd b u
    refine ⟨-ι (xcoord M.Rn b), ι z2 - ι z1, by rw [neg_mul_neg]; exact M.hDm.symm, ?_⟩
    have := congrArg (ι (V := V)) hz
    simp only [map_add, map_mul, map_ofNat] at this
    rw [← hu] at this
    rw [ha, hA, M.hc]
    have hB' : (ι E.Bn : DiffRing V) = ι b + 2 := by rw [hbB]; ring
    rw [hB']
    linear_combination -this

set_option maxHeartbeats 2000000 in
/-- **The signed projector.** `σ X = 2^R` with `x 8 = σ |c|`. -/
theorem projector (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0)
    (E : EarlyFold p x κ ω Λ ψ wt) (M : MainIndex p x κ ω Λ ψ wt E)
    (Fi : FirstIndex p x κ ω Λ ψ wt E M) :
    ∃ σ : DiffRing V, (σ = 1 ∨ σ = -1) ∧ x 8 = σ * ι E.cn ∧
      σ * (𝓡).X = ι (Exp.exp M.Rn) := by
  have hB : 0 < (𝓡).Budget := budget_pos ψ wt hp h hwt hz
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two M.hodd
  obtain ⟨xn, hxn⟩ := abs_eq_ι (𝓡).X
  obtain ⟨d, z, hdd, hd⟩ := signed_main ψ wt E M
  have hHK := H_dvd_q15_Kq5 ψ wt hp h hwt hz
  have hlarge := H_large ψ wt hp h hwt hz E M Fi t xn ht hxn
  -- the sign of `c`
  obtain ⟨σ, hσ, hcσ⟩ : ∃ σ : DiffRing V, (σ = 1 ∨ σ = -1) ∧ x 8 = σ * ι E.cn := by
    rcases eq_or_eq_neg_abs (x 8) with h' | h' <;> rw [E.hcn] at h'
    · exact ⟨1, Or.inl rfl, by rw [h', one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h']; ring⟩
  have hσσ : σ * σ = 1 := by rcases hσ with h' | h' <;> rw [h'] <;> ring
  refine ⟨σ, hσ, hcσ, ?_⟩
  set T : DiffRing V := ι (Exp.exp M.Rn) with hT
  set X' := σ * (𝓡).X with hX'
  have hnorm : d * d = 1 + ((𝓡).a * (𝓡).a + (4 * (𝓡).a + 3)) * ι E.cn * ι E.cn := by
    rw [hdd, Dm_eq, Delta_def, H_def, hcσ]
    linear_combination (((𝓡).a * (𝓡).a + (4 * (𝓡).a + 3)) * ι E.cn * ι E.cn) * hσσ
  have hK : (4 * (𝓡).a + 3) ∣
      (𝓡).q ^ 15 * (X' * X' + 2 * (𝓡).a * X' * ι E.cn - 1) ^ 5 := by
    have e' : X' * X' + 2 * (𝓡).a * X' * ι E.cn - 1 = Kq p x κ ω Λ ψ wt := by
      unfold Kq; rw [hX', hcσ]
      linear_combination ((𝓡).X * (𝓡).X) * hσσ
    rw [e', ← H_def]; exact hHK
  have h5 := fifth_power_mul (𝓡).a (ι E.cn) d T X' z ((𝓡).q ^ 15) hd hnorm hK
  rw [← H_def] at h5
  -- the height
  have hX66 : Exp.exp (66 : V) ≤ xn := by
    apply ι_le_ι.mp
    rw [← hxn]
    have := abs_X_ge p x κ ω Λ ψ wt hp
    have e' : (ι (Exp.exp (66 : V)) : DiffRing V) = 2 ^ 66 := by
      have h' := exp_nat (V := V) 66
      rw [Nat.cast_ofNat] at h'
      rw [h', map_pow, map_ofNat]
    rw [e']; exact this
  have ht40 : (40 : V) ≤ t := by
    apply ι_le_ι.mp
    have h4 : (4080 : DiffRing V) ≤ ι M.Rn := by
      have := R_ge p x κ ω Λ ψ wt hp (signs ψ wt hp h hB); rwa [M.hR] at this
    rw [ht] at h4; simp only [map_add, map_mul, map_ofNat, map_one] at h4; rw [map_ofNat]
    linarith
  have hheight := height_power15 xn t hX66 ht40
  have hT1 : (1 : DiffRing V) ≤ T := by rw [hT, ← map_one ι]; exact ι_le_ι.mpr (one_le_exp _)
  have hX'abs : |X'| = ι xn := by
    rw [hX', abs_mul, hxn]; rcases hσ with h' | h' <;> rw [h'] <;> simp
  have hxn1 : (1 : DiffRing V) ≤ ι xn := by
    rw [← hxn]; have := abs_X_ge p x κ ω Λ ψ wt hp
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
  have hq15 : |(𝓡).q| ^ 15 ≤ (ι xn : DiffRing V) ^ 15 := by
    have h4 := abs_X p x κ ω Λ ψ wt
    rw [hxn] at h4
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (𝓡).q]) 15
  have hP5 : |(𝓡).q ^ 15 * ((X' - T) * (T * X' + 1)) ^ 5| < |(𝓡).H| := by
    rw [abs_mul, abs_pow, abs_pow]
    have h1 : |(X' - T) * (T * X' + 1)| ^ 5 ≤ ((ι xn * (T + 1)) ^ 2) ^ 5 :=
      pow_le_pow_left₀ (abs_nonneg _) hP 5
    have h12 : |(𝓡).q| ^ 15 * |(X' - T) * (T * X' + 1)| ^ 5 ≤
        (ι xn : DiffRing V) ^ 15 * ((ι xn * (T + 1)) ^ 2) ^ 5 :=
      mul_le_mul hq15 h1 (pow_nonneg (abs_nonneg _) 5) (pow_nonneg (ι_nonneg _) 15)
    have h2 : (ι xn : DiffRing V) ^ 15 * ((ι xn * (T + 1)) ^ 2) ^ 5 =
        ι ((xn * (Exp.exp M.Rn + 1)) ^ 10 * xn ^ 15) := by
      rw [hT]; simp only [map_pow, map_mul, map_add, map_one]; ring
    have h3 : (ι ((xn * (Exp.exp M.Rn + 1)) ^ 10 * xn ^ 15) : DiffRing V) ≤
        ι (xn * power (xn - 3) t) := by
      apply ι_le_ι.mpr; rw [ht]; exact hheight
    linarith
  have h0 := eq_zero_of_dvd_lt h5 hP5
  have h0' : ((X' - T) * (T * X' + 1)) ^ 5 = 0 := by
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd ((pow_eq_zero_iff (by norm_num : (15 : ℕ) ≠ 0)).mp h')
        (q_ne p x κ ω Λ ψ wt hp)
    · exact h'
  rcases mul_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp h0') with h' | h'
  · linear_combination h'
  · exfalso
    have hT2 : (2 : DiffRing V) ≤ T := by
      have h1 : (1 : V) ≤ M.Rn := pos_iff_one_le.mp M.hRpos
      have h2 : (2 : V) ≤ Exp.exp M.Rn := by
        calc (2 : V) = Exp.exp 1 := exp_one.symm
          _ ≤ Exp.exp M.Rn := exp_monotone_le.mpr h1
      have h3 := ι_le_ι.mpr h2
      rw [map_ofNat] at h3
      rw [hT]; exact h3
    have hX'1 : 1 ≤ |X'| := by rw [hX'abs]; exact hxn1
    have : |T * X'| = 1 := by
      rw [show T * X' = -1 by linear_combination h', abs_neg, abs_one]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T)] at this
    nlinarith

end Regs

#print axioms fifth_power_mul
#print axioms height_power15
#print axioms signed_main
#print axioms projector

end DiophantineConsistency.LCProjector
